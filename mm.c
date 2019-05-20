/*
 * mm.c 
 *
 * free blocks : set last bit as 0 with size
 * allocated blocks : set last bit as 1 with size
 *
 * every block has header/footer that stores the above information
 * first 4 bytes stores nothing
 * next 4 bytes stores the size with the alloc/free bit
 * next bytes are for users
 * last 8 bytes of block : the former 4 bytes stores nothing
 * the latter 4 bytes stores the size with the alloc/free bit
 *
 * free blocks are somewhat different
 * first 8 bytes(header) are set as above
 * next 4 bytes(+8~+11) stores the address of the same part of the previous list entry
 * and then next 4 bytes(+12~+15) stores the address of the same part of the next list entry
 *
 * segregated list stores the address of +12~15 part
 *
 * when entries are added(blocks are freed), the entries become the first entry of each list
 * when deleted, update the information of next/prev blocks(if exists)
 *
 * in malloc, use the entries to see if sbrk is needed or not
 *
 * similar to the segregated list implementation on the book
 * but less space efficient than the implementation
 *
 * there is a segregated list of free blocks
 * total 22 lists and each for entries that corresponds to the size
 *
 * the list is stored in heap
 * which is allocated by mem_sbrk in mm_init
 *
 * since there can be small allocations that hinder the total performance
 * makes small space for small blocks that is too small for big blocks
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// mask out low bit -- from slide
#define GET_SIZE_WITH_POS(p) (*p & -2)
#define GET_ALLOC_WITH_POS(p) (*p & 1)
#define SET_ALLOC_VAL(size) (size | 1)
#define SET_FREE_VAL(info) ((info >> 1) << 1)

#define LISTLENGTH 22

//go to specific position
#define PREVINT(p) ( (int *)p - 1 )
#define NEXTINT(p) ( (int *)p + 1 )
#define PREV2INT(p) ( (int *)p - 2 )
#define NEXT2INT(p) ( (int *)p + 2 )
#define PREV3INT(p) ( (int *)p - 3 )
#define NEXT3INT(p) ( (int *)p + 3 )
#define PREV4INT(p) ( (int *)p - 4 )
#define NEXT4INT(p) ( (int *)p + 4 )

//go and get the value from the specific position
#define INTVAL(p) ( *( (int *)p ) )
#define PREVINTVAL(p) ( *( (int *)p - 1 ) )
#define NEXTINTVAL(p) ( *( (int *)p + 1 ) )
#define PREV2INTVAL(p) ( *( (int *)p - 2 ) )
#define NEXT2INTVAL(p) ( *( (int *)p + 2 ) )
#define PREV3INTVAL(p) ( *( (int *)p - 3 ) )
#define NEXT3INTVAL(p) ( *( (int *)p + 3 ) )

//getting positions or values according to their usages
#define DIVUSRPTR(p, size) ((void *)((int *)((char *)p + size + 16) - 1))
#define BACKWARDINT(start_ptr, tempSize) ( (int *)( (char *)start_ptr - tempSize ) - 4 )
#define FORWARDINT(last_ptr, tempSize)  ( (int *)( (void *)last_ptr + tempSize ) + 4 )
#define SECONDINFOINTVAL(p, contentsize) ( *( (int *)( (char *)p + contentsize ) + 3 ) )

//some constant values used to check the system specification
const int SIZE_OF_POINTER = sizeof(void **); //4
const int SIZE_OF_SIZE_T = SIZE_T_SIZE; //4
const int SIZE_OF_INFOS = ALIGN(SIZE_T_SIZE) * 2; //16

static char *mem_start_brk; //same usage as the one in memlib.c
static void **seg_list; //segregated list
static char *mm_start_brk; //after the list info
static char *mem_max_addr; //similar usage as the one in memlib.c

static int m_count; //checking small block requests

int mm_check(void);

/* 
 * mm_init - initialize the malloc package.
 * gets space for the segregated list and set some information
 */
int mm_init(void)
{
	int i;

	m_count = 0;
	mem_start_brk = (char *)mem_heap_lo(); //stores also here
	seg_list = (void **)mem_start_brk; //start point of seg list
    if(mem_sbrk(SIZE_OF_POINTER * LISTLENGTH) == (void *)-1) //get space for list 
	{
		printf("init failed\n");
		return -1;
	}
	//initialize to NULL
	for(i=0;i<LISTLENGTH;i++)
		seg_list[i] = NULL;

	mm_start_brk = (char *)mem_heap_hi() + 1; //for usr space - where the heap space for user request starts

    return 0;
}

/* 
 * remove_entry - removes an entry from the list.
 * changes the information of prev/next block(if exists)
 */
void remove_entry(void *next_p)
{
	//gets next_p
	int *next = (int *)INTVAL(next_p);
	
	//if there is a next entry
	if(next != NULL)  
		//go to next and update prev info
		PREVINTVAL(INTVAL(next_p)) = PREVINTVAL(next_p);

	//go to prev and update next info
	//if in usr space
	if((char *)NEXTINT(PREVINTVAL(next_p)) > mm_start_brk)
		NEXTINTVAL(PREVINTVAL(next_p)) = INTVAL(next_p);
	
	else {
		//prev info
		INTVAL(PREVINTVAL(next_p)) = INTVAL(next_p);
	}
}

/* 
 * add_to_list_usr - add a free block to the list.
 * gets ptr and size, add a block as one of the first entry
 */
void add_to_list_usr(void *ptr, int size)
{
	//ptr : user ptr
	int temp_val = size;
	int cnt_bit = 0; // # of bits for size
	
	int index;

	if(size == 0)
		return;

	while(temp_val != 0)
	{
		cnt_bit++;
		temp_val /= 2;
	}
	index = cnt_bit - 4;

	//get seg_list value and put into 'next' part
	NEXTINTVAL(ptr) = (int)(seg_list[index]);

	//usr ptr pos : prev address [art
	INTVAL(ptr) = (int)(&(seg_list[index]));

	//if there is next entry, update prev part
	if(NEXTINTVAL(ptr) != (int)NULL)
		PREVINTVAL(NEXTINTVAL(ptr)) = (int)ptr;

	//seg_list only needs to have 'next'
	seg_list[index] = (void *)NEXTINT(ptr);
}

/* 
 * set_info_free - set free bits for the input block.
 * use macros
 */
void set_info_free(void *p, int size)
{
	//gets info part
	//sets in each info as free
	INTVAL(p) = SET_FREE_VAL(size);
	SECONDINFOINTVAL(PREVINT(p), size) = SET_FREE_VAL(size);
}

/* 
 * mm_malloc - Always allocate a block whose size is a multiple of the alignment.
 * use segregated list and firstly, find in the list
 * if there is no entry, mem_sbrk
 */
void *mm_malloc(size_t size)
{
	int newsize = ALIGN(size + SIZE_OF_INFOS);
	int contentsize = ALIGN(size);
	void *p = NULL;
	int i = 0;
	int temp_val = contentsize;
	void *next_p = NULL;
	int found = 0; // found or not
	int diff;
	void *temp_ptr;
	int sizediv;

	//if getting really small block requests
	if(newsize <= 32) {
		if(m_count == 0 || m_count == 4) {
			//make a space for small blocks.
			mm_free(mm_malloc(ALIGN(size) * 4 + 16 * 3));
			m_count = 1;
		}
		else
			m_count++;
	}
	//if getting yet small block requests
	else if(newsize <= 80) {
		if(m_count == 0 || m_count == 6) {
			//make a space for small blocks.
			mm_free(mm_malloc(ALIGN(size) * 6 + 16 * 5));
			m_count = 1;
		}
		else
			m_count++;
	}

	//getting starting index
	while(temp_val != 0)
	{
		i++;
		temp_val /= 2;
	}

	//find from the matching index
	for(i=i-4;i<LISTLENGTH;i++)
	{
		next_p = seg_list[i];
		
		while(next_p != NULL)
		{
			//check the size difference
			diff = GET_SIZE_WITH_POS(PREV2INT(next_p)) - contentsize;

			if(diff == 0)
			{
				p = PREV3INT(next_p);
				remove_entry(next_p); // remove from list
				found = 1;
			}
			else if(diff >= 16)
			{
				p = PREV3INT(next_p);
				remove_entry(next_p); // remove from list

				//after division, left ones
				sizediv = diff - 16;
				temp_ptr = DIVUSRPTR(next_p, contentsize);

				// set infos on the divided block -- size & free bit
				set_info_free( (void *)PREVINT(temp_ptr) , sizediv);
				add_to_list_usr(temp_ptr, sizediv);
				found = 1;
			}
			else
				next_p = (void *)INTVAL(next_p);

			if(found)
				break;
		}
		if(found)
			break;
	}

	//if none
	if(!found)
	    p = mem_sbrk(newsize);

    if (p == (void *)-1)
		return NULL;
    else
	{
		//set information
		NEXTINTVAL(p) = SET_ALLOC_VAL(contentsize);
		SECONDINFOINTVAL(p, contentsize) = SET_ALLOC_VAL(contentsize);
        return (void *)((char *)p + SIZE_OF_SIZE_T);
    }
}

/* 
 * coalesce - checks if there are free blocks adjacent to the input free block.
 * just using the info(header/footer), go backward and forward
 */
void coalesce(void *ptr)
{
	//gets user ptr

	//ptr is not yet added to the list

	//start_ptr will always point to info part while traversing
	int *start_ptr = PREV3INT(ptr);
	//size of next corresponding block while traversing
	int tempSize;
	//total coalesced size
	int totalSize = GET_SIZE_WITH_POS(PREVINT(ptr));
	//initially points to next ptr
	int *last_ptr = FORWARDINT(PREVINT(ptr), totalSize);

	//backward : not to pass the boundary mm_start_brk
	while( (char *)start_ptr >= mm_start_brk ) {
		//start with second info part of previous block
		//if allocated 
		if(GET_ALLOC_WITH_POS(start_ptr))
			break;

		//if not allocated, get size
		tempSize = GET_SIZE_WITH_POS(start_ptr);

		//add tempSize + 16(redundant info space) to the total
		totalSize += (tempSize + 16);

		//move to next corresponding position
		start_ptr = BACKWARDINT(start_ptr, tempSize);

		//remove the entry from the list
		if(tempSize != 0)
			remove_entry( (void *)NEXT4INT(start_ptr) );
	}
	//finished backward coalescing

	mem_max_addr = (char *)( mem_heap_hi() );

	//foreward : not to go foreward if exceeds max_addr
	while( (char *)last_ptr < mem_max_addr )
	{
		if(GET_ALLOC_WITH_POS(last_ptr))
			break;

		//if not allocated, get size
		tempSize = GET_SIZE_WITH_POS(last_ptr);
		//add tempSize + 16(redundant info space) to the total
		totalSize += (tempSize + 16);

		//remove the entry from the list
		if(tempSize != 0)
			remove_entry( (void *)NEXT2INT(last_ptr) );

		last_ptr = FORWARDINT(last_ptr, tempSize);
	}
	//set info and add to list
	set_info_free( NEXT2INT(start_ptr), totalSize );
	add_to_list_usr( NEXT3INT(start_ptr) , totalSize );
}

/*
 * mm_free - Freeing a block.
 */
void mm_free(void *ptr)
{
	//gets user ptr
	int size = GET_SIZE_WITH_POS(PREVINT(ptr));
	//sets information
	PREVINTVAL(ptr) = SET_FREE_VAL(PREVINTVAL(ptr));
	SECONDINFOINTVAL(PREV2INT(ptr), size) = SET_FREE_VAL(PREVINTVAL(ptr));
	//coalesce
	coalesce(ptr);
}

/* 
 * check_last_usr - checks if an input block is the last block in the heap.
 * make use of the mem_heap_hi() function
 */
int check_last_usr(void *ptr) 
{
	void *next = FORWARDINT(PREVINT(ptr), GET_SIZE_WITH_POS(PREVINT(ptr)));
	void *high = mem_heap_hi();
	if(next >= high) {
		return 1;
	}
	return 0;
}

/*
 * mm_realloc - checks if can coalesce. otherwise, mm_malloc
 * very similar to coalesce
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize = GET_SIZE_WITH_POS(PREVINT(ptr));
	
	//gets user ptr
	//start_ptr will always point to info part while traversing
	int *start_ptr = PREV3INT(ptr);
	//size of next corresponding block while traversing
	int tempSize;
	//total coalesced size
	int totalSize = GET_SIZE_WITH_POS(PREVINT(ptr));
	//initially points to next ptr
	int *last_ptr = FORWARDINT(PREVINT(ptr), totalSize);
	//if possible
	int possible = 0;
	//ptr for iteration
	int *itr_ptr = PREV3INT(ptr);
	void *start_info_ptr;
	int sizediv;
	void *div_ptr;
	int newsize = ALIGN(size);
	int i;
	int diff;
	void *temp_ptr;

    if (newsize < copySize)
      copySize = newsize;
	   
	if(ptr == NULL) {
		return mm_malloc(size);
	}
	if(size == 0) {
		mm_free(ptr);
		return NULL;
	}

	if(totalSize == newsize)
		return ptr;
	else if(totalSize >= newsize + 16) {
		start_info_ptr = (void *)PREVINT(ptr);
		sizediv = totalSize - newsize - 16;

		//set info on new free block
		INTVAL(start_info_ptr) = SET_ALLOC_VAL(newsize);
		SECONDINFOINTVAL(PREVINT(start_info_ptr), newsize) = SET_ALLOC_VAL(newsize);

		//divide
		div_ptr = DIVUSRPTR( NEXT2INT(start_info_ptr), newsize );
		set_info_free( (void *)PREVINT(div_ptr) , sizediv);
		add_to_list_usr(div_ptr , sizediv);
	
		return ptr;
	}

	//if last, just sbrk the difference
	if(totalSize < newsize && check_last_usr(ptr)){

		diff = newsize - totalSize;
		temp_ptr = mem_sbrk(diff);//just the difference

		if(temp_ptr == (void *)-1) {
			printf("mem_sbrk failed\n");
			exit(1);
		}

		//set information
		PREVINTVAL(ptr) = SET_ALLOC_VAL(newsize);
		SECONDINFOINTVAL(PREV2INT(ptr), newsize) = SET_ALLOC_VAL(newsize);
		return ptr;
	}

	//backward : not to pass the boundary mm_start_brk
	while( (char *)start_ptr >= mm_start_brk ) {

		//start with second info part of previous block
		//if allocated 
		if(GET_ALLOC_WITH_POS(start_ptr))
			break;

		//if not allocated, get newsize
		tempSize = GET_SIZE_WITH_POS(start_ptr);
		//add tempSize + 16(redundant info space) to the total
		totalSize += (tempSize + 16);
		//move to next corresponding position
		start_ptr = BACKWARDINT(start_ptr, tempSize);

		if(totalSize >= newsize + 16 || totalSize == newsize) {
			possible = 1;
			break;
		}
	}
	//finished backward coalescing in realloc

	//if not possible continue forward realloc coalescing
	if(!possible) {
		mem_max_addr = (char *)( mem_heap_hi() );

		//foreward : not to go foreward if exceeds max_addr
		while( (char *)last_ptr < mem_max_addr )
		{
			if(GET_ALLOC_WITH_POS(last_ptr))
				break;

			//if not allocated, get newsize
			tempSize = GET_SIZE_WITH_POS(last_ptr);
			//add tempSize + 16(redundant info space) to the total
			totalSize += (tempSize + 16);
	
			last_ptr = FORWARDINT(last_ptr, tempSize);

			if(totalSize >= newsize + 16 || totalSize == newsize) {
				possible = 1;
				break;
			}
		}
	}
	tempSize = GET_SIZE_WITH_POS(itr_ptr);

	//remove all in the route
	if(possible) {
		//backward
		while(itr_ptr > start_ptr)
		{
			itr_ptr = BACKWARDINT(itr_ptr, tempSize);
			tempSize = GET_SIZE_WITH_POS(itr_ptr);
			//remove the entry from the list
			remove_entry( (void *)NEXT4INT(itr_ptr) );
		}
	
		tempSize = GET_SIZE_WITH_POS(PREVINT(ptr));
		itr_ptr = FORWARDINT(PREVINT(ptr), tempSize);

		//forward
		while(itr_ptr < last_ptr)
		{
			//remove the entry from the list
			remove_entry( (void *)NEXT2INT(itr_ptr) );
			tempSize = GET_SIZE_WITH_POS(itr_ptr);
			itr_ptr = FORWARDINT(last_ptr, tempSize);
		}

		//when all entry removed from free list, their info not needed
		start_info_ptr = NEXT2INT(start_ptr);
		//before (possible) overwriting infos
		newptr = (void *)NEXTINT(start_info_ptr);

		for(i=0;i<copySize;i++)
			((char *)newptr)[i] = ((char *)oldptr)[i];

		if(totalSize != newsize)
		{
			sizediv = totalSize - newsize - 16;
			//set info on new free block
			INTVAL(start_info_ptr) = SET_ALLOC_VAL(newsize);
			SECONDINFOINTVAL(PREVINT(start_info_ptr), newsize) = SET_ALLOC_VAL(newsize);

			//divide
			div_ptr = DIVUSRPTR( NEXT2INT(start_info_ptr), newsize );
			set_info_free( (void *)PREVINT(div_ptr) , sizediv);
			add_to_list_usr(div_ptr , sizediv);
		}
	}
	else {
    		newptr = mm_malloc(size);
	}

    if (newptr == NULL)
      return NULL;

	if(!possible)
	{
    	memcpy(newptr, oldptr, copySize);
	   	mm_free(oldptr);
	}
    return newptr;
}

/*
 * check_if_in_list_usr - checks if an input free block is in list.
 * just traverse through the list
 */
int check_if_in_list_usr(void *ptr, int size)
{
	void *traverse;
	void *compare = (void *)NEXTINT(ptr);
	int index;
	int cnt_bit = 0;
	int found = 0;

	if(size == 0)
		return 1;

	while(size != 0)
	{
		cnt_bit++;
		size /= 2;
	}

	index = cnt_bit - 4;
	
	traverse = seg_list[index];

	while( traverse != NULL )
	{
		if(traverse == compare) {
			found = 1;
			break;
		}
		traverse = (void *)INTVAL(traverse);
	}

	return found;
}

/*
 * mm_check - checks heap consistency.
 * traverse by address
 * then traverse with list information
 */
int mm_check(void)
{
	//traverse heap space
	void *traverse = (void *)NEXTINT(mm_start_brk);
	int *traverse2;
	void *high = mem_heap_hi();
	int prev = 1;  //0 : previous free block, 1 : previous allocated block
	int valid = 1;
	int i = 0;
	void *prevptr;
	
	//traverse by address
	while( traverse < high ) {
		if(GET_ALLOC_WITH_POS((int *)traverse))
			prev = 1;
		else {
			if(prev == 0) {
				printf("ptr %p not coalesced", NEXTINT(traverse));
				valid = 0;
			}
			if(!check_if_in_list_usr((void *)NEXTINT(traverse), GET_SIZE_WITH_POS((int *)traverse))){
				valid = 0;
				printf("ptr %p not in list\n", NEXTINT(traverse));
			}
			prev = 0;
		}
		prevptr = traverse;
		traverse = (void *)FORWARDINT( traverse, GET_SIZE_WITH_POS((int *)traverse) );
		if(INTVAL(prevptr) != PREV2INTVAL(traverse))
			printf("ptr %p different header/footer\n", NEXTINT(prevptr));
	}

	//traverse with list
	while ( i < LISTLENGTH )
	{
		if(seg_list[i] == NULL){
			i++;
			continue;
		}
		else {
			traverse2 = (int *)(seg_list[i]);
			while(traverse2 != NULL)
			{
				if(GET_ALLOC_WITH_POS(PREV2INT(traverse2)))
				{
					valid = 0;
					printf("ptr %p in free list but alloc bit set", PREVINT(traverse2) );
				}
				traverse2 = (int *)INTVAL(traverse2);
			}
		}
		i++;
	}

	if(valid){
		return 1;
	}
	else {
		printf("invalid\n");
		return 0;
	}
}

