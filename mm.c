/*
 * mm.c
 *
 * Malloc Lab Checkpoint
 * Lu Liu (Andrew ID: lul3)
 *
 * Strategy: use explicit list to maintain free blocks in it, and exploit FIFO
 * strategy. When a block is freed, it would be added at the beginning of the
 * list. And when a block need to be allocated, scan the list from the
 * beginning, and use the first fit free block in the explicit list.
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want debugging output, uncomment the following.  Be sure not
 * to have debugging enabled in your final submission
 */
//#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#define dbg_checkheap(...) mm_checkheap(__VA_ARGS__)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#define dbg_requires(...)
#define dbg_ensures(...)
#define dbg_checkheap(...)
#define dbg_printheap(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16

#define NUM_LIST 8

 /* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*wsize;          // double word size (bytes)
static const size_t min_block_size = 2*dsize; // Minimum block size
static const size_t chunksize = (1 << 8);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

typedef struct block
{
    word_t header;

    union data {
        char payload[0];
        struct list_ptr
        {
            struct block *next;
            struct block *prev;
        } ptr;
    } data;
} block_t;

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool prev_alloc, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);
static bool get_prev_alloc(block_t *block);

static void write_header(
    block_t *block, size_t size, bool prev_alloc, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);
static void write_next_prev_alloc(block_t *block, size_t size, bool blloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static void insert_to_free_list(block_t *block);
static void remove_block_from_list(block_t* block);
static block_t* get_prev_free(block_t *block);
static block_t* get_next_free(block_t *block);
static void link_blocks(block_t *prev, block_t* next);
static int find_fit_segregated_list(int size);
static void print_free_list();

bool mm_checkheap(int lineno);

static block_t *heap_listp = NULL;
static int *segregated_size = NULL;
static block_t **segregated_list = NULL;

/*
 * Initialize: return false on error, true on success.
 */
bool mm_init(void) {
    dbg_printf("Start init.\n");
    int block_size, i;

    segregated_size = (int *)(mem_sbrk(sizeof(int) * NUM_LIST));
    segregated_list = (block_t**)(mem_sbrk(sizeof(block_t*) * NUM_LIST));
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));
    dbg_printf("segregated_size: %p, segregated_list: %p - %p\n",
        (void*)segregated_size, (void*)segregated_list,
        (void*)(&segregated_list[NUM_LIST - 1]));
    if (start == (void *)-1)
    {
        return false;
    }
    start[0] = pack(0, true, true);
    start[1] = pack(1, true, true);
    heap_listp = (block_t *) &(start[1]);

    block_size = 50;
    for (i = 0; i < NUM_LIST - 1; i++) {
        segregated_size[i] = block_size;
        block_size = (int)(block_size * 1.7 + 33);
    }
    for (i = 0; i < NUM_LIST; i++) {
        segregated_list[i] = NULL;
    }

    dbg_printf("Before extend heap.\n");
    if (extend_heap(chunksize) == NULL) {
      return false;
    }

    dbg_printf("Finish init.\n");

    print_free_list();
    return true;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    size_t asize;
    size_t extendsize;
    block_t *block;
    void *bp = NULL;

    dbg_printf("Malloc size %d.\n", (int)size);

    if (heap_listp == NULL)
    {
        mm_init();
    }

    if (size == 0)
    {
        return bp;
    }

    asize = max(round_up(size + wsize, dsize), min_block_size);
    block = find_fit(asize);
    dbg_printf("Fit block: %p\n", (void*)block);

    if (block == NULL)
    {
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }
        // print_free_list();
    }

    place(block, asize);
    dbg_printf("Place block: %p\n", (void*)block);
    bp = header_to_payload(block);

    dbg_printf("Malloc size %zd on address %p.\n", size, bp);
    dbg_ensures(mm_checkheap);
    return bp;
}

/*
 * free
 */
void free (void *ptr) {
    if (ptr == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(ptr);
    size_t size = get_size(block);
    dbg_printf("Free block at addr %p with size %d.\n", (void*)block, (int)size);

    write_header(block, size, get_prev_alloc(block), false);
    write_footer(block, size, false);
    write_next_prev_alloc(block, size, false);

    coalesce(block);
    dbg_ensures(mm_checkheap);
}

/*
 * realloc
 */
void *realloc(void *oldptr, size_t size) {
    block_t *block = payload_to_header(oldptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(oldptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (oldptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (!newptr)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, oldptr, copysize);

    // Free the old block
    free(oldptr);

    return newptr;
}

/*
 * calloc
 * This function is not tested by mdriver
 */
void *calloc (size_t nmemb, size_t size) {
    void *bp;
    size_t asize = nmemb * size;

    if (asize/nmemb != size)
    // Multiplication overflowed
    return NULL;

    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void *p) {
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno) {
    block_t *block;
    word_t header;
    word_t *footerp;

    for (block = heap_listp; get_size(block) > 0;
                             block = find_next(block))
    {
        header = block->header;
        footerp = (word_t *)((block->data.payload) + get_size(block) - dsize);
        if (*footerp != header)
        {
            dbg_printf("[Heap Error on line %d] different header and footer \
                        for block on %p\n", lineno, (void*)block);
            return false;
        }
    }

    // for (block = free_list; block != NULL; block = get_next_free(block))
    // {
    //     if (get_alloc(block) > 0)
    //     {
    //         dbg_printf("[Heap Error on line %d] Allocated block %p is in \
    //                     free list.\n", lineno, (void*)block);
    //         return false;
    //     }
    // }
    return NULL; // no fit found
}

/*
 * extend_heap: Extends the heap with the requested number of bytes, and
 *              recreates epilogue header. Returns a pointer to the result of
 *              coalescing the newly-created block with previous free block, if
 *              applicable, or NULL in failure.
 */
static block_t *extend_heap(size_t size)
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    dbg_printf("Extend heap.\n");
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }

    // Initialize free block header/footer
    dbg_printf("Initialize free block header/footer.\n");
    block_t *block = payload_to_header(bp);
    write_header(block, size, get_prev_alloc(block), false);
    write_footer(block, size, false);
    write_next_prev_alloc(block, size, false);
    dbg_printf("[Extend heap] extend block: %p, header: %p\n",
        (void*)block, (void*)block->header);

    // Create new epilogue header
    dbg_printf("Create new epilogue header..\n");
    block_t *block_next = find_next(block);
    write_header(block_next, 0, false, true);
    dbg_printf("[Extend heap] Next block: %p, header: %p\n",
        (void*)block_next, (void*)block_next->header);

    // Coalesce in case the previous block was free
    dbg_printf("Coalesce\n");
    return coalesce(block);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, data));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(&(block->data));
}

/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

static word_t *find_footer(block_t *block)
{
    return (word_t *)((block->data.payload)
        + get_size(block) - dsize);
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    dbg_printf("[find prev] footer: %d (at %p)\n",
        (int)*footerp, (void*)footerp);
    return (block_t *)((char *)block - size);
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}


/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

static bool get_prev_alloc(block_t *block)
{
    return (bool) ((block->header >> 1) & 1);
}

static word_t change_prev_alloc(word_t word, bool prev_alloc)
{
    return (word & ~2) | (prev_alloc << 1);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size,
    bool prev_alloc, bool alloc)
{
    block->header = pack(size, prev_alloc, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->data.payload)
        + get_size(block) - dsize);
    *footerp = pack(size, false, alloc);
    dbg_printf("[write footer] %p => %d\n", (void*)footerp, (int)*footerp);
}

static void write_next_prev_alloc(block_t *block, size_t size, bool alloc)
{
    block_t *next_block = find_next(block);
    next_block->header = change_prev_alloc(next_block->header, alloc);
}

/**
 * Link up two blocks in the explicit list.
 */
static void link_blocks(block_t *prev, block_t* next)
{
    if (prev != NULL)
        prev->data.ptr.next = next;
    if (next != NULL)
        next->data.ptr.prev = prev;
}

/**
 * Get previous free block in free list.
 */
static block_t* get_prev_free(block_t *block)
{
    return block->data.ptr.prev;
}

/**
 * Get next free block in free list.
 */
static block_t* get_next_free(block_t *block)
{
    return block->data.ptr.next;
}

/*
 * place: Places block with size of asize at the start of bp. If the remaining
 *        size is at least the minimum block size, then split the block to the
 *        the allocated block and the remaining block as free, which is then
 *        inserted into the free list. Requires that the block is
 *        initially unallocated.
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);
    dbg_printf("[place] block addr: %p, size: %d csize: %d\n",
            (void*)block, (int)asize, (int)csize);

    if ((csize - asize) >= min_block_size)
    {
        dbg_printf("[place] Case 1\n");
        block_t *block_next;
        write_header(block, asize, get_prev_alloc(block), true);
        write_next_prev_alloc(block, asize, true);
        dbg_printf("[place] block: %p, header: %p\n",
            (void*)block, (void*)block->header);

        block_next = find_next(block);
        write_header(block_next, csize-asize, true, false);
        write_footer(block_next, csize-asize, false);
        // word_t *footer = find_footer(block_next);
        // dbg_printf("[place] next block: %p, header: %p footer: %d(addr=%p)\n",
        //     (void*)block_next, (void*)block_next->header,
        //     (int)*footer, (void*)footer);

        remove_block_from_list(block);
        insert_to_free_list(block_next);
    }

    else
    {
        dbg_printf("[place] Case 2\n");
        write_header(block, csize, get_prev_alloc(block), true);
        write_next_prev_alloc(block, csize, true);
        remove_block_from_list(block);
    }
}

/*
 * find_fit: Looks for a free block with at least asize bytes with
 *           first-fit policy. Returns NULL if none is found.
 */
static block_t *find_fit(size_t asize)
{
    block_t *block, *selected;
    int i;
    size_t block_size, min_block;

    dbg_printf("[find_fit] asize = %d\n", (int)asize);

    int index = find_fit_segregated_list(asize);
    for (i = index; i < NUM_LIST; i++) {
        min_block = 0x7FFFFFFF;
        for (block = segregated_list[i]; block != NULL;
            block = get_next_free(block)) {
            block_size = get_size(block);
            if (block_size == asize)
                return block;
            if (asize <= block_size && block_size < min_block &&
                block_size - asize >= min_block_size) {
                min_block = block_size;
                selected = block;
            }
        }
        if (min_block < 0x7FFFFFFF)
            return selected;
    }
    dbg_printf("[find_fit] NULL\n");
    return NULL; // No fit block found.
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool prev_alloc, bool alloc)
{
    return size | alloc | (prev_alloc << 1);
}

/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

static int get_list_index(block_t* block)
{
    for (int i = 0; i < NUM_LIST; i++) {
        if (segregated_list[i] == block)
            return i;
    }
    return 0;
}

/* Coalesce: Coalesces current block with previous and next blocks if either
 *           or both are unallocated; otherwise the block is not modified.
 *           Returns pointer to the coalesced block. After coalescing, the
 *           immediate contiguous previous and next blocks must be allocated.
 */
static block_t *coalesce(block_t * block)
{
    block_t *block_prev = NULL;
    block_t *block_next = find_next(block);
    dbg_printf("[Coalesce]next: %p  prev: %p\n",
        (void*)block_next, (void*)block_prev);

    bool prev_alloc = get_prev_alloc(block);
    bool next_alloc = get_alloc(block_next);
    dbg_printf("[Coalesce]next alloc: %d  prev alloc: %d\n",
        (int)next_alloc, (int)prev_alloc);
    size_t size = get_size(block);

    if (prev_alloc && next_alloc)              // Case 1
    {
        insert_to_free_list(block);
        return block;
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
        size += get_size(block_next);
        dbg_printf("[Coalesce]next: %p  prev: %p\n",
            (void*)block_next, (void*)block_prev);
        remove_block_from_list(block_next);
        write_header(block, size, get_prev_alloc(block), false);
        write_footer(block, size, false);
        insert_to_free_list(block);
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
        block_prev = find_prev(block);
        dbg_printf("[Coalesce]next: %p  prev: %p\n",
            (void*)block_next, (void*)block_prev);
        size += get_size(block_prev);
        remove_block_from_list(block_prev);
        write_header(block_prev, size, get_prev_alloc(block_prev), false);
        write_footer(block_prev, size, false);
        block = block_prev;
        insert_to_free_list(block);
    }

    else                                        // Case 4
    {
        block_prev = find_prev(block);
        dbg_printf("[Coalesce]next: %p  prev: %p\n",
            (void*)block_next, (void*)block_prev);
        size += get_size(block_next) + get_size(block_prev);
        remove_block_from_list(block_prev);
        remove_block_from_list(block_next);
        write_header(block_prev, size, get_prev_alloc(block_prev), false);
        write_footer(block_prev, size, false);
        insert_to_free_list(block_prev);

        block = block_prev;
    }
    return block;
}

/**
 * Insert a new free block into the free list.
 */
static void insert_to_free_list(block_t *block)
{
    int index = find_fit_segregated_list(get_size(block));
    block_t *selected = segregated_list[index];

    dbg_printf("[Insert to free list] %p index: %d\n", (void*)block, index);
    if (selected == NULL) {
        link_blocks(NULL, block);
        link_blocks(block, NULL);
        segregated_list[index] = block;
        print_free_list();
        return;
    }

    link_blocks(NULL, block);
    link_blocks(block, selected);
    segregated_list[index] = block;
    print_free_list();
    return;
}

static void remove_block_from_list(block_t* block)
{
    block_t *prev = get_prev_free(block);
    block_t *next = get_next_free(block);
    dbg_printf("[Remove block from list] %p prev: %p, next: %p\n",
        (void*)block, (void*)prev, (void*)next);
    if (prev == NULL)
        segregated_list[get_list_index(block)] = next;
    link_blocks(prev, next);
    print_free_list();
}

static int find_fit_segregated_list(int size)
{
    for (int i = 0; i < NUM_LIST - 1; i++) {
        if (segregated_size[i] >= size) {
            return i;
        }
    }
    return NUM_LIST - 1;
}

static void print_free_list()
{
    block_t *block_iter;

    dbg_printf("-----------------Free List------------------\n");
    for (int i = 0; i < NUM_LIST; i++) {
        for (block_iter = segregated_list[i]; block_iter != NULL;
                block_iter = get_next_free(block_iter)) {
            dbg_printf("[Free list %d] block addr: %p, block size: %d prev: %p next: %p\n",
                    i, (void*)block_iter, (int)get_size(block_iter),
                    (void*)get_prev_free(block_iter), (void*)get_next_free(block_iter));
        }
    }
    dbg_printf("-----------------Free List END------------------\n");
}
