#include "threads/thread.h"
#include <debug.h>
#include <stddef.h>
#include <random.h>
#include <stdio.h>
#include <string.h>
#include "threads/flags.h"
#include "threads/interrupt.h"
#include "threads/intr-stubs.h"
#include "threads/palloc.h"
#include "threads/switch.h"
#include "threads/synch.h"
#include "threads/vaddr.h"
#ifdef USERPROG
#include "userprog/process.h"
#endif
#include "devices/timer.h"

// Definição de macros para manipulação de números de ponto fixo

#define F (1 << 14)

// Converte inteiro para ponto fixo.
#define INT_TO_FP(n) ((n) * F)

// Converte ponto fixo para inteiro (arredonda para zero).
#define FP_TO_INT(x) ((x) / F)

// Converte ponto fixo para inteiro (arredonda para o mais próximo).
#define FP_TO_INT_ROUND(x) ((x) >= 0 ? ((x) + F / 2) / F : ((x) - F / 2) / F)

// Soma dois números de ponto fixo.
#define ADD_FP(x, y) ((x) + (y))

// Subtrai dois números de ponto fixo.
#define SUB_FP(x, y) ((x) - (y))

// Adiciona um inteiro a um número de ponto fixo.
#define ADD_FP_INT(x, n) ((x) + (n) * F)

// Subtrai um inteiro de um número de ponto fixo.
#define SUB_FP_INT(x, n) ((x) - (n) * F)

// Multiplica dois números de ponto fixo.
#define MUL_FP(x, y) (((int64_t)(x)) * (y) / F)

// Multiplica um número de ponto fixo por um inteiro.
#define MUL_FP_INT(x, n) ((x) * (n))

// Divide dois números de ponto fixo.
#define DIV_FP(x, y) (((int64_t)(x)) * F / (y))

// Divide um número de ponto fixo por um inteiro.
#define DIV_FP_INT(x, n) ((x) / (n))
// Adição de um número inteiro a um número de ponto fixo
#define ADD_MIX(x, n) ((x) + (n) * F)

// Subtração de um número inteiro de um número de ponto fixo
#define SUB_MIX(x, n) ((x) - (n) * F)

// Divisão de um número de ponto fixo por um número inteiro
#define DIV_MIX(x, n) ((x) / (n))
// Multiplicação de um número de ponto fixo por um número inteiro
#define MUL_MIX(x, n) ((x) * (n))
#define FP_INT_PART(x) ((x) / F)

// Multiplicação de um número de ponto fixo por um número inteiro (definição adicional)
#define FLOAT_MULT_MIX(x, n) MUL_MIX(x, n)

// Arredondamento de um número de ponto fixo
#define FLOAT_ROUND(x) (FP_TO_INT((x) + F / 2))

/* Random value for struct thread's `magic' member.
   Used to detect stack overflow.  See the big comment at the top
   of thread.h for details. */
#define THREAD_MAGIC 0xcd6abf4b
/* List of processes in THREAD_READY state, that is, processes
   that are ready to run but not actually running. */
static struct list ready_list;

// lista dos processos que estão dormindo
static struct list sleep_list;

/* List of all processes.  Processes are added to this list
   when they are first scheduled and removed when they exit. */
static struct list all_list;

/* Idle thread. */
static struct thread *idle_thread;

/* Initial thread, the thread running init.c:main(). */
static struct thread *initial_thread;

/* Lock used by allocate_tid(). */
static struct lock tid_lock;

/* Stack frame for kernel_thread(). */
struct kernel_thread_frame
{
  void *eip;             /* Return address. */
  thread_func *function; /* Function to call. */
  void *aux;             /* Auxiliary data for function. */
};

/* Statistics. */
static long long idle_ticks;   /* # of timer ticks spent idle. */
static long long kernel_ticks; /* # of timer ticks in kernel threads. */
static long long user_ticks;   /* # of timer ticks in user programs. */

/* Scheduling. */
#define TIME_SLICE 4          /* # of timer ticks to give each thread. */
static unsigned thread_ticks; /* # of timer ticks since last yield. */

static int load_avg; /*Numero de threads prontos para execucao no ultimo minuto*/

/* If false (default), use round-robin scheduler.
   If true, use multi-level feedback queue scheduler.
   Controlled by kernel command-line option "-o mlfqs". */
bool thread_mlfqs;
bool time_to_wakeup_comparator(const struct list_elem *a, const struct list_elem *b, void *aux UNUSED);
static void kernel_thread(thread_func *, void *aux);

static void idle(void *aux UNUSED);
static struct thread *running_thread(void);
static struct thread *next_thread_to_run(void);
static void init_thread(struct thread *, const char *name, int priority);
static bool is_thread(struct thread *) UNUSED;
static void *alloc_frame(struct thread *, size_t size);
static void schedule(void);
void thread_schedule_tail(struct thread *prev);
static tid_t allocate_tid(void);
bool thread_priority_comparator(const struct list_elem *a, const struct list_elem *b, void *aux UNUSED);

/* Initializes the threading system by transforming the code
   that's currently running into a thread.  This can't work in
   general and it is possible in this case only because loader.S
   was careful to put the bottom of the stack at a page boundary.

   Also initializes the run queue and the tid lock.

   After calling this function, be sure to initialize the page
   allocator before trying to create any threads with
   thread_create().

   It is not safe to call thread_current() until this function
   finishes. */

// Verifica se a prioridade da thread atual é menor do que a prioridade da primeira thread na lista de threads prontas, caso seja, cede o lock para a thread de maior prioridade
void check_yield(void)
{
  if (thread_current()->priority < list_entry(list_begin(&ready_list), struct thread, elem)->priority)
  {
    thread_yield();
  }
}
void thread_init(void)
{
  ASSERT(intr_get_level() == INTR_OFF);

  lock_init(&tid_lock);
  list_init(&ready_list);
  list_init(&sleep_list);
  list_init(&all_list);

  /* Set up a thread structure for the running thread. */
  initial_thread = running_thread();
  init_thread(initial_thread, "main", PRI_DEFAULT);
  initial_thread->status = THREAD_RUNNING;
  initial_thread->tid = allocate_tid();
}

/* Starts preemptive thread scheduling by enabling interrupts.
   Also creates the idle thread. */
void thread_start(void)
{
  /* Create the idle thread. */
  struct semaphore idle_started;
  sema_init(&idle_started, 0);
  thread_create("idle", PRI_MIN, idle, &idle_started);

  /* Start preemptive thread scheduling. */
  intr_enable();

  /* Wait for the idle thread to initialize idle_thread. */
  sema_down(&idle_started);
}

/* Called by the timer interrupt handler at each timer tick.
   Thus, this function runs in an external interrupt context. */
void thread_tick(void)
{
  struct thread *t = thread_current();

  /* Update statistics. */
  if (t == idle_thread)
    idle_ticks++;
#ifdef USERPROG
  else if (t->pagedir != NULL)
    user_ticks++;
#endif
  else
    kernel_ticks++;

  /* Enforce preemption. */
  if (++thread_ticks >= TIME_SLICE)
    intr_yield_on_return();

  if (timer_ticks() % TIMER_FREQ == 0) // Faz verificação a cada segundo, caso o mlfqs esteja ativado, para calcular o tempo de cpu (da thread) e o load_avg (numero de threads prontas para serem executadas no ultimo minuto)
  {
    calculate_load_avg();
    update_recent_cpu();
  }
  if (thread_mlfqs && t != idle_thread) // Se o mlfqs estiver ativado e a thread atual não for a idle_thread, incrementa a recent_cpu em 1 unidade
  {
    t->recent_cpu = ADD_FP_INT(t->recent_cpu, 1);
  }

  if (timer_ticks() % 4 == 0) // A cada 4 segundos atualiza as prioridades das threads
  {
    update_priorities();
  }
}

/* Prints thread statistics. */
void thread_print_stats(void)
{
  printf("Thread: %lld idle ticks, %lld kernel ticks, %lld user ticks\n",
         idle_ticks, kernel_ticks, user_ticks);
}

/* Creates a new kernel thread named NAME with the given initial
   PRIORITY, which executes FUNCTION passing AUX as the argument,
   and adds it to the ready queue.  Returns the thread identifier
   for the new thread, or TID_ERROR if creation fails.

   If thread_start() has been called, then the new thread may be
   scheduled before thread_create() returns.  It could even exit
   before thread_create() returns.  Contrariwise, the original
   thread may run for any amount of time before the new thread is
   scheduled.  Use a semaphore or some other form of
   synchronization if you need to ensure ordering.

   The code provided sets the new thread's `priority' member to
   PRIORITY, but no actual priority scheduling is implemented.
   Priority scheduling is the goal of Problem 1-3. */
tid_t thread_create(const char *name, int priority,
                    thread_func *function, void *aux)
{
  struct thread *t;
  struct kernel_thread_frame *kf;
  struct switch_entry_frame *ef;
  struct switch_threads_frame *sf;
  tid_t tid;

  ASSERT(function != NULL);

  /* Allocate thread. */
  t = palloc_get_page(PAL_ZERO);
  if (t == NULL)
    return TID_ERROR;

  /* Initialize thread. */
  init_thread(t, name, priority);
  tid = t->tid = allocate_tid();

  /* Stack frame for kernel_thread(). */
  kf = alloc_frame(t, sizeof *kf);
  kf->eip = NULL;
  kf->function = function;
  kf->aux = aux;

  /* Stack frame for switch_entry(). */
  ef = alloc_frame(t, sizeof *ef);
  ef->eip = (void (*)(void))kernel_thread;

  /* Stack frame for switch_threads(). */
  sf = alloc_frame(t, sizeof *sf);
  sf->eip = switch_entry;
  sf->ebp = 0;

  /* Add to run queue. */
  thread_unblock(t);

  return tid;
}

/* Puts the current thread to sleep.  It will not be scheduled
   again until awoken by thread_unblock().

   This function must be called with interrupts turned off.  It
   is usually a better idea to use one of the synchronization
   primitives in synch.h. */
void thread_block(void)
{
  ASSERT(!intr_context());
  ASSERT(intr_get_level() == INTR_OFF);

  thread_current()->status = THREAD_BLOCKED;
  schedule();
}

/* Transitions a blocked thread T to the ready-to-run state.
   This is an error if T is not blocked.  (Use thread_yield() to
   make the running thread ready.)

   This function does not preempt the running thread.  This can
   be important: if the caller had disabled interrupts itself,
   it may expect that it can atomically unblock a thread and
   update other data. */
void thread_unblock(struct thread *t)
{
  enum intr_level old_level;

  ASSERT(is_thread(t));

  old_level = intr_disable();
  ASSERT(t->status == THREAD_BLOCKED);
  list_insert_ordered(&ready_list, &t->elem, thread_priority_comparator, NULL);
  t->status = THREAD_READY;
  intr_set_level(old_level);
}

/* Returns the name of the running thread. */
const char *
thread_name(void)
{
  return thread_current()->name;
}

/* Returns the running thread.
   This is running_thread() plus a couple of sanity checks.
   See the big comment at the top of thread.h for details. */
struct thread *
thread_current(void)
{
  struct thread *t = running_thread();

  /* Make sure T is really a thread.
     If either of these assertions fire, then your thread may
     have overflowed its stack.  Each thread has less than 4 kB
     of stack, so a few big automatic arrays or moderate
     recursion can cause stack overflow. */
  ASSERT(is_thread(t));
  ASSERT(t->status == THREAD_RUNNING);

  return t;
}

/* Returns the running thread's tid. */
tid_t thread_tid(void)
{
  return thread_current()->tid;
}

/* Deschedules the current thread and destroys it.  Never
   returns to the caller. */
void thread_exit(void)
{
  ASSERT(!intr_context());

#ifdef USERPROG
  process_exit();
#endif

  /* Remove thread from all threads list, set our status to dying,
     and schedule another process.  That process will destroy us
     when it calls thread_schedule_tail(). */
  intr_disable();
  list_remove(&thread_current()->allelem);
  thread_current()->status = THREAD_DYING;
  schedule();
  NOT_REACHED();
}

/* Yields the CPU.  The current thread is not put to sleep and
   may be scheduled again immediately at the scheduler's whim. */
void thread_yield(void)
{
  struct thread *cur = thread_current();
  enum intr_level old_level;

  ASSERT(!intr_context());

  old_level = intr_disable();
  if (cur != idle_thread)
    list_insert_ordered(&ready_list, &cur->elem, thread_priority_comparator, NULL);
  cur->status = THREAD_READY;
  schedule();
  intr_set_level(old_level);
}

void thread_sleep(int64_t ticks)
{
  struct thread *cur = thread_current(); // retorna a thread atualmente em execucao e armazena em cur
  enum intr_level old_level;             // Variavel que vai armazenar o estado anterior

  ASSERT(!intr_context()); // Garante que nao esta sendo chamada em contexto de interrupcao

  old_level = intr_disable(); // Desabilita as interrupcoes e salva o estado anterior na variavel old_level

  if (cur != idle_thread) // Verifica se a thread atual nao e a idle_thread,pois a idle_thread e uma thread ociosa
  {
    cur->time_to_wakeup = ticks;                                                   // Define o tempo de despertar da thread atual
    list_insert_ordered(&sleep_list, &cur->elem, time_to_wakeup_comparator, NULL); // Insere a thread na lista de threads adormecidas de forma ordenada
  }
  cur->status = THREAD_BLOCKED; // Muda o status da thread para bloqueada
  schedule();                   //  aciona o escalonador novamente
  intr_set_level(old_level);    // Restaura o estado das interrupções
}

void thread_wakeup(void)
{
  struct list_elem *e = list_begin(&sleep_list); // e aponta para o começo da sleep_list
  if (list_empty(&sleep_list))                   //  Verifica se a lista de threads adormecidas até o final
  {
    return; // Se estiver vazia, sai da função
  }
  while (e != list_end(&sleep_list)) // Percorre a lista de threads adormecidas até o final
  {
    struct thread *t = list_entry(e, struct thread, elem); // Obtém a estrutura das thread a partir do elemento da lista
    if (t->time_to_wakeup > timer_ticks())                 // Verificamos se a thread ainda deve continuar dormindo
      break;                                               // Caso simm sai do loop, pois as threads seguintes também não precisam ser acordadas
    enum intr_level old_level = intr_disable();            // Desabilita as interrupções e salva o estado anterior das interrupções na var. old_level
    e = list_remove(e);                                    // Remove a thread atual da lista sleep_list
    thread_unblock(t);                                     // Desbloqueia a thread para permitir que ela seja escalonada
    intr_set_level(old_level);                             // Restaura o estado anterior das interrupções  }
  }
}

/* Invoke function 'func' on all threads, passing along 'aux'.
   This function must be called with interrupts off. */
void thread_foreach(thread_action_func *func, void *aux)
{
  struct list_elem *e;

  ASSERT(intr_get_level() == INTR_OFF);

  for (e = list_begin(&all_list); e != list_end(&all_list);
       e = list_next(e))
  {
    struct thread *t = list_entry(e, struct thread, allelem);
    func(t, aux);
  }
}

/*Funcao que compara as prioridades e retorna um booleano dizendo se tem prioridade maior ou nao*/
bool thread_priority_comparator(const struct list_elem *a, const struct list_elem *b, void *aux UNUSED)
{
  const struct thread *t_a = list_entry(a, struct thread, elem);
  const struct thread *t_b = list_entry(b, struct thread, elem);
  return t_a->priority > t_b->priority;
}
/* Sets the current thread's priority to NEW_PRIORITY. */
void thread_set_priority(int new_priority)
{
  //  seta uma nova prioridade a thread
  struct thread *cur = thread_current(); //  thread atual
  cur->priority = new_priority;
  if (!list_empty(&ready_list) && cur->priority < list_entry(list_front(&ready_list), struct thread, elem)->priority)
  {
    thread_yield();
  }
}

/* Returns the current thread's priority. */
int thread_get_priority(void)
{
  return thread_current()->priority;
}

void thread_calculate_recent_cpu(struct thread *t)
{
  if (t != idle_thread) // Só atualizamos o recent_cpu se a threadt não for idle_thread
  {
    int load_avg = MUL_FP_INT(load_avg, 2); // multiplica load_avg por 2
    t->recent_cpu = MUL_FP(DIV_FP_INT(load_avg * 2, load_avg * 2 + 1), t->recent_cpu) + INT_TO_FP(t->nice);
  }
}

// Função responsável por calcular a média de carga do sistema
void calculate_load_avg()
{
  int ready_threads = list_size(&ready_list); // Obtém o número de threads prontas na lista de threads prontas
  if (thread_current() != idle_thread)
  {
    ready_threads++; // Incrementa p número de threads prontas se a thread atual nã for a idle_thread
  }
  load_avg = ADD_FP(DIV_FP(MUL_FP(INT_TO_FP(59), load_avg), INT_TO_FP(60)), DIV_FP(INT_TO_FP(ready_threads), INT_TO_FP(60)));
}

/* Sets the current thread's nice value to NICE. */
void thread_set_nice(int new_nice)
{
  struct thread *cur = thread_current();
  cur->nice = new_nice;

  // recalcula a prioridade
  thread_calculate_priority(cur);

  // Se a nova prioridade for menor que a prioridade do primeiro da lista de prontos, yield
  if (!list_empty(&ready_list) && cur->priority < list_entry(list_front(&ready_list), struct thread, elem)->priority)
  {
    thread_yield(); // Fazer que a thread atual cesa voluntariamente a CPU
  }
}

/* Returns the current thread's nice value. */
int thread_get_nice(void)
{
  struct thread *cur = thread_current();
  return FLOAT_ROUND(cur->nice);
}

/*Calcula a prioridade apos o new_nice*/
void thread_calculate_priority(struct thread *t)
{
  if (t != idle_thread)
  {
    t->priority = FP_INT_PART(SUB_MIX(SUB_FP(INT_TO_FP(PRI_MAX), DIV_MIX(t->recent_cpu, 4)), (t->nice * 2)));
    if (t->priority < PRI_MIN)
    {
      t->priority = PRI_MIN;
    }
    else if (t->priority > PRI_MAX)
    {
      t->priority = PRI_MAX;
    }
  }
}

//  Garantir que todas as threads no sistema tenham suas prioridades atualizadas
void update_priorities()
{
  struct list_elem *e;
  for (e = list_begin(&all_list); e != list_end(&all_list); e = list_next(e))
  {
    struct thread *t = list_entry(e, struct thread, allelem);
    thread_calculate_priority(t);
  }
}
// Retorna 100 vezes a média de carga do sistema
int thread_get_load_avg(void)
{
  return FLOAT_ROUND(FLOAT_MULT_MIX(load_avg, 100)); // Retorna o valor aproximado para inteiro
}

// Retorna100 vezes o valor atual do recent_cpu
int thread_get_recent_cpu(void)
{
  struct thread *cur = thread_current();
  return FLOAT_ROUND(FLOAT_MULT_MIX(cur->recent_cpu, 100)); // Retorna o valor aproximado para inteiro
}

/*Funcao que faz o calculo de quanto tempo de CPU cada thread recebeu recentemente*/
void update_recent_cpu()
{
  struct list_elem *e;
  //  e passa por toda a all_list
  for (e = list_begin(&all_list); e != list_end(&all_list); e = list_next(e))
  {
    struct thread *t = list_entry(e, struct thread, allelem);
    if (t != idle_thread)
    {
      int load = MUL_FP_INT(load_avg, 2);                                                                                      //  multiplica o load_avg por 2
      t->recent_cpu = ADD_MIX(MUL_FP(DIV_FP(MUL_MIX(load_avg, 2), ADD_MIX(MUL_MIX(load_avg, 2), 1)), t->recent_cpu), t->nice); //  Faz o calculo usando ponto flutuante
    }
  }
}

/* Idle thread.  Executes when no other thread is ready to run.

   The idle thread is initially put on the ready list by
   thread_start().  It will be scheduled once initially, at which
   point it initializes idle_thread, "up"s the semaphore passed
   to it to enable thread_start() to continue, and immediately
   blocks.  After that, the idle thread never appears in the
   ready list.  It is returned by next_thread_to_run() as a
   special case when the ready list is empty. */
static void
idle(void *idle_started_ UNUSED)
{
  struct semaphore *idle_started = idle_started_;
  idle_thread = thread_current();
  sema_up(idle_started);

  for (;;)
  {
    /* Let someone else run. */
    intr_disable();
    thread_block();

    /* Re-enable interrupts and wait for the next one.

       The `sti' instruction disables interrupts until the
       completion of the next instruction, so these two
       instructions are executed atomically.  This atomicity is
       important; otherwise, an interrupt could be handled
       between re-enabling interrupts and waiting for the next
       one to occur, wasting as much as one clock tick worth of
       time.

       See [IA32-v2a] "HLT", [IA32-v2b] "STI", and [IA32-v3a]
       7.11.1 "HLT Instruction". */
    asm volatile("sti; hlt" : : : "memory");
  }
}

/* Function used as the basis for a kernel thread. */
static void
kernel_thread(thread_func *function, void *aux)
{
  ASSERT(function != NULL);

  intr_enable(); /* The scheduler runs with interrupts off. */
  function(aux); /* Execute the thread function. */
  thread_exit(); /* If function() returns, kill the thread. */
}

/* Returns the running thread. */
struct thread *
running_thread(void)
{
  uint32_t *esp;

  /* Copy the CPU's stack pointer into `esp', and then round that
     down to the start of a page.  Because `struct thread' is
     always at the beginning of a page and the stack pointer is
     somewhere in the middle, this locates the curent thread. */
  asm("mov %%esp, %0" : "=g"(esp));
  return pg_round_down(esp);
}

/* Returns true if T appears to point to a valid thread. */
static bool
is_thread(struct thread *t)
{
  return t != NULL && t->magic == THREAD_MAGIC;
}

/* Does basic initialization of T as a blocked thread named
   NAME. */
static void
init_thread(struct thread *t, const char *name, int priority)
{
  enum intr_level old_level;

  ASSERT(t != NULL);
  ASSERT(PRI_MIN <= priority && priority <= PRI_MAX);
  ASSERT(name != NULL);

  load_avg = 0; // Inicializa a variavel global load_avg
  memset(t, 0, sizeof *t);
  t->status = THREAD_BLOCKED;
  strlcpy(t->name, name, sizeof t->name);
  t->stack = (uint8_t *)t + PGSIZE;
  t->priority = priority; // A primeira thread recebe a prioridade passada como argumento, as demais recebema prioridade do pai
  t->magic = THREAD_MAGIC;

  old_level = intr_disable();
  list_push_back(&all_list, &t->allelem);
  intr_set_level(old_level);
}

/* Allocates a SIZE-byte frame at the top of thread T's stack and
   returns a pointer to the frame's base. */
static void *
alloc_frame(struct thread *t, size_t size)
{
  /* Stack data is always allocated in word-size units. */
  ASSERT(is_thread(t));
  ASSERT(size % sizeof(uint32_t) == 0);

  t->stack -= size;
  return t->stack;
}

/* Chooses and returns the next thread to be scheduled.  Should
   return a thread from the run queue, unless the run queue is
   empty.  (If the running thread can continue running, then it
   will be in the run queue.)  If the run queue is empty, return
   idle_thread. */
static struct thread *
next_thread_to_run(void)
{
  if (list_empty(&ready_list))
    return idle_thread;
  else
    return list_entry(list_pop_front(&ready_list), struct thread, elem);
}

/* Completes a thread switch by activating the new thread's page
   tables, and, if the previous thread is dying, destroying it.

   At this function's invocation, we just switched from thread
   PREV, the new thread is already running, and interrupts are
   still disabled.  This function is normally invoked by
   thread_schedule() as its final action before returning, but
   the first time a thread is scheduled it is called by
   switch_entry() (see switch.S).

   It's not safe to call printf() until the thread switch is
   complete.  In practice that means that printf()s should be
   added at the end of the function.

   After this function and its caller returns, the thread switch
   is complete. */
void thread_schedule_tail(struct thread *prev)
{
  struct thread *cur = running_thread();

  ASSERT(intr_get_level() == INTR_OFF);

  /* Mark us as running. */
  cur->status = THREAD_RUNNING;

  /* Start new time slice. */
  thread_ticks = 0;

#ifdef USERPROG
  /* Activate the new address space. */
  process_activate();
#endif

  /* If the thread we switched from is dying, destroy its struct
     thread.  This must happen late so that thread_exit() doesn't
     pull out the rug under itself.  (We don't free
     initial_thread because its memory was not obtained via
     palloc().) */
  if (prev != NULL && prev->status == THREAD_DYING && prev != initial_thread)
  {
    ASSERT(prev != cur);
    palloc_free_page(prev);
  }
}

/* Schedules a new process.  At entry, interrupts must be off and
   the running process's state must have been changed from
   running to some other state.  This function finds another
   thread to run and switches to it.

   It's not safe to call printf() until thread_schedule_tail()
   has completed. */
static void
schedule(void)
{
  struct thread *cur = running_thread();
  struct thread *next = next_thread_to_run();
  struct thread *prev = NULL;

  ASSERT(intr_get_level() == INTR_OFF);
  ASSERT(cur->status != THREAD_RUNNING);
  ASSERT(is_thread(next));

  if (cur != next)
    prev = switch_threads(cur, next);
  thread_schedule_tail(prev);
}

/* Returns a tid to use for a new thread. */
static tid_t
allocate_tid(void)
{
  static tid_t next_tid = 1;
  tid_t tid;

  lock_acquire(&tid_lock);
  tid = next_tid++;
  lock_release(&tid_lock);

  return tid;
}

// Função para comparar o tempo de despertar de duas threads
//  Caso t_a->time_to_wakeup < t_b->time_to_wakeup for verdade, a função retorna true, caso não false
bool time_to_wakeup_comparator(const struct list_elem *a, const struct list_elem *b, void *aux UNUSED)
{
  const struct thread *t_a = list_entry(a, struct thread, elem);
  const struct thread *t_b = list_entry(b, struct thread, elem);
  return t_a->time_to_wakeup < t_b->time_to_wakeup;
}

/* Offset of `stack' member within `struct thread'.
   Used by switch.S, which can't figure it out on its own. */
uint32_t thread_stack_ofs = offsetof(struct thread, stack);