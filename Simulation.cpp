#include<iostream>
#include<fstream>
#include<stdlib.h>
#include<time.h>
#include<iomanip>
#include<assert.h>

// Memory size
#define MEMSIZE 30000

// Machine population limits
#define MAXALIVE 100
#define MINFREEMEM 0.35

// Machine size limits
#define MINSIZE 12
#define MAXSIZE 300

// Machine data structure size
#define LOOPSTACKSIZE 4
#define DATASTACKSIZE 8
#define NREGS 4

// Simulation max time
#define SIMSTEPS 200000
// Information output regularity
#define PRINTINFOTIME 50000
// Machine steps per simulation step
#define STEPSPERCYCLE 50
// Machine error penalty
#define ERRORSTEPS 10

// enable assertions
#define NDEBUG
 
#define MUTCHANCE 1000000
// 1/MUTCHANCE =
//  chance a random instruction is written instead of intended one
#define ERRORCHANCE 1000000
// 1/ERRORCHANCE =
//  chance a random instruction is executed instead of intended one

/* TODO
 * 
 */

// **************************************************************** //
//                    Classes and structures
// **************************************************************** //

// stack using array
struct StackUnderflow {};
struct StackOverflow {};
template<class T> class Stack {
  private:
    int top;
    int capacity;
    T* storage;
  public:
    Stack(int cap) {
      if (cap <= 0)
        cap = 1;
      top = 0;
      capacity = cap;
      storage = new T[capacity];
    }
    void push(T value) {
      if (top == capacity)
        throw StackOverflow();
      storage[top++] = value;
    }
    T pop() {
      if (top == 0)
        throw StackUnderflow();
      return storage[--top];
    }
    bool isEmpty() {
      if (top == 0) return true;
      else return false;
    }
    ~Stack() {
      delete[] storage;
    }
    void resetStack() {
      top = 0;
    }
    void printStack() {
      int i;
      for (i=top-1; i > -1; i--) {
          std::cout << storage[i] << ",";
      }
      std::cout << "\n";
    }
};

// queue using linked list
struct QueueEmpty {};
template<class T> struct node {
  T val;
  node* next; // closer to rear
  node* prev; // closer to front
};
template<class T> class Queue {
  private:
    node<T>* front;
    node<T>* rear;
  public:
    Queue() {
      front = NULL;
      rear = NULL;
    }
    void enqueue(T value) {
      // add to rear of queue
      node<T>* temp = new node<T>;
      temp->val = value;
      temp->next = NULL; 
      temp->prev = rear;
      
      if (front == NULL) front = temp;
      else rear->next = temp;
      rear = temp;
    }
    T dequeue() {
      // remove from front of queue
      if (front == NULL) throw QueueEmpty();
      
      node<T>* temp = new node<T>;
      temp = front;
      front = front->next;
      
      T value = temp->val;
      delete temp;
      return value;
    }
    node<T>* getHead() {
      return front;
    }
    void promote(node<T>* n) {
      // if front, can't promote
      if (n == front) return;
      // swap values with prev
      T temp = n->val;
      n->val = n->prev->val;
      n->prev->val = temp;
    }
    void demote(node<T>* n) {
      // if rear, can't demote
      if (n == rear) return;
      // swap values with next
      T temp = n->val;
      n->val = n->next->val;
      n->next->val = temp;
    }
    bool isEmpty() {
      if (front == NULL) return true;
      else return false;
    }
};

// basic machine structure
class Machine {
  public:
    int location;
    int IP;
    short* reg;
    Stack<short>* dataStack;
    Stack<short>* loopStack;
    
    int mySize;
    int childLoc;
    int childSize;
    
    Machine(int loc, int size) {
      location = loc;
      IP = loc;
      
      reg = new short[ NREGS ];
      int i;
      for (i=0; i<NREGS; i++)
        reg[i]=0;
      dataStack = new Stack<short>( DATASTACKSIZE );
      loopStack = new Stack<short>( LOOPSTACKSIZE );
      
      mySize = size;
      childLoc = -1;
      childSize = -1;
    }
    ~Machine() {
      delete[] reg;
      delete dataStack;
      delete loopStack;
    }
};

/*
Instruction set

NOP   Do nothing
MAL   Allocate memory at dataStack.pop() of length dataStack.pop()
        Return 1 if success, 0 if failure
FORK  Create new CPU at allocated memory
        Return 1 if success, 0 if failure
COPY  Copy instruction at dataStack.pop() to dataStack.pop()
        Return 1 if success, 0 if faulure
WRITE Write dataStack.pop() to dataStack.pop()
        Return 1 if success, 0 if faulure
READ  dataStack.push( instruction at dataStack.pop() )
DO    loopStack.push( IP )
LOOP  IP = loopStack.pop()
SLTZ  if (dataStack.pop() < 0) IP++
SEZ   if (dataStack.pop() = 0) IP++
LOAD  dataStack.push( reg[dataStack.pop()] )
STORE reg[dataStack.pop()] = dataStack.pop()
PUSH  IP++
      dataStack.push( instruction at IP )
POP   dataStack.pop()
INC   dataStack.push( dataStack.pop() + 1 )
DEC   dataStack.push( dataStack.pop() - 1 )
ALU   OP = dataStack.pop()
        OP can be any of:
          ADD SUB DIV MUL
          GRE LES EQU
          AND  OR XOR 
      dataStack.push( dataStack.pop() OP dataStack.pop() )
RAND  dataStack.push(rand)
*/
// instructions available
enum instr {
  NOP , MAL  , FORK, COPY, WRITE, READ,
  DO  , LOOP , SLTZ, SEZ ,
  LOAD, STORE, PUSH, POP ,
  INC , DEC  , ALU , RAND
};
// operations ALU can perform
enum func {
  ADD, SUB, DIV, MUL,
  GRE, LES, EQU, 
  AND, OR , XOR
};

// **************************************************************** //
//                   Declare global variables
// **************************************************************** //

// main memory space (array of signed bytes)
signed char* memory = new signed char[MEMSIZE];

// memory protections (array of Machine*)
Machine** memProtect = new Machine*[MEMSIZE];

// CPUs (Queue of Machine* on heap)
Queue<Machine*>* CPUs = new Queue<Machine*>();


// **************************************************************** //
//                           Functions
// **************************************************************** //

int mapToRange(int val, int range) {
  if (val >= range || val < 0) {
    val %= range;
    if (val < 0) val += range;
  }
  assert(val >= 0 && val < range);
  return val;
}

// **************************************************************** //
// Memory protection functions

bool memOwned(int loc, int len, Machine* m) {
  assert(loc >= 0 && loc < MEMSIZE);
  int i,j;
  for (i=loc,j=0; j < len; i++,j++) {
    if (i >= MEMSIZE) i=0;
    if (memProtect[i] != m) return false;
  }
  return true;
}
bool memFree(int loc, int len) {
  assert(loc >= 0 && loc < MEMSIZE);
  return memOwned(loc, len, NULL);
}
void memAlloc(int loc, int len, Machine* m) {
  assert(loc >= 0 && loc < MEMSIZE);
  int i,j;
  for (i=loc,j=0; j < len; i++,j++) {
    if (i >= MEMSIZE) i=0;
    memProtect[i] = m;
  }
  assert(memOwned(loc, len, m));
}
void memDealloc(int loc, int len) {
  memAlloc(loc, len, NULL);
  assert(memFree(loc, len));
}
int memAvailable() {
  int i,j;
  for (i=0,j=0; i < MEMSIZE; i++) 
    if (memProtect[i] == NULL) j++;
  return j;
}

// **************************************************************** //
// Machine creation/deletion

void createCPU(Machine* parent) {
  int loc = parent->childLoc;
  int len = parent->childSize;
  assert(loc >= 0 && loc < MEMSIZE);
  assert(memOwned(loc, len, parent));
  
  Machine* child = new Machine(loc, len);
  CPUs->enqueue(child);
  memAlloc(loc, len, child);
  
  parent->childLoc = -1;
  parent->childSize = -1;
}
void killCPU() {
  Machine* m = CPUs->getHead()->val;
  
  int loc = m->location;
  int len = m->mySize;
  
  assert(memOwned(loc, len, m));
  memDealloc(loc, len);
  
  if (m->childLoc != -1) {
    assert(memOwned(m->childLoc, m->childSize, m));
    memDealloc(m->childLoc, m->childSize);
  }
  CPUs->dequeue();
  delete m;
}

// **************************************************************** //
// Execution of 1 instruction for 1 machine
// Return 0 if no errors, else number specific to error

class ExecutionError {};
int execute(Machine* m) {
  instr i = static_cast<instr>(memory[m->IP]);
  // execution error
  if (rand()%ERRORCHANCE < 1) i = static_cast<instr>(rand()%20);
  
  try {
    switch(i) {
      case NOP:
        break;
        
      case MAL:
      { if (m->childLoc != -1) {
          assert(memOwned(m->childLoc, m->childSize, m));
          memDealloc(m->childLoc, m->childSize);
          m->childLoc = -1; m->childSize = -1;
        }
          
        int start = mapToRange( m->dataStack->pop() + m->location, MEMSIZE);
        int len = m->dataStack->pop();
        
        if (len > m->mySize*3 || len < MINSIZE || len > MAXSIZE) {
          m->dataStack->push(0);
          throw ExecutionError();
        }
        
        if (memFree(start, len)) {
          memAlloc(start, len, m);
          m->childLoc = start;
          m->childSize = len;
          m->dataStack->push(1);
        } else {
          m->dataStack->push(0);
          // don't throw error here
          // as CPU has no way of knowing if memory is free...
          //throw ExecutionError();
        }
        break;}
        
      case FORK:
      { if (m->childLoc == -1) {m->dataStack->push(0); throw ExecutionError();}
        createCPU(m);
        m->dataStack->push(1);
        break;}
        
      case COPY:
      { int to =   mapToRange( m->dataStack->pop() + m->location, MEMSIZE);
        int from = mapToRange( m->dataStack->pop() + m->location, MEMSIZE);
        
        if (memProtect[to] == NULL || memProtect[to] == m) {
          memory[to] = memory[from];
          // mutations
          if (rand()%MUTCHANCE < 1) memory[to] = rand()%20;
          m->dataStack->push(1);
        } else {
          m->dataStack->push(0);
          throw ExecutionError();
        }
        break;}
        
      case WRITE:
      { int to = mapToRange( m->dataStack->pop() + m->location, MEMSIZE);
        signed char cmd = m->dataStack->pop();
        
        if (memProtect[to] == NULL || memProtect[to] == m) {
          memory[to] = cmd;
          // mutations
          if (rand()%MUTCHANCE < 1) memory[to] = rand()%20;
          m->dataStack->push(1);
        } else {
          m->dataStack->push(0);
          throw ExecutionError();
        }
        break;}
        
      case READ:
        m->dataStack->push( memory[ (m->dataStack->pop() + 
                                  m->location) % MEMSIZE ] );
        break;
        
      case DO:
        m->loopStack->push( m->IP );
        break;
      case LOOP:
        m->IP = m->loopStack->pop() - 1;
        if (m->IP < 0) m->IP += MEMSIZE;
        break;
        
      case SLTZ:
        if (m->dataStack->pop() < 0) {
          m->IP++;
          if (m->IP >= MEMSIZE) m->IP -= MEMSIZE;
          if (memory[m->IP] == LOOP) m->loopStack->pop();
        }
        break;
      case SEZ:
        if (m->dataStack->pop() == 0) {
          m->IP++;
          if (m->IP >= MEMSIZE) m->IP -= MEMSIZE;
          if (memory[m->IP] == LOOP) m->loopStack->pop();
        }
        break;
        
      case LOAD:
      { int regNum = mapToRange( m->dataStack->pop() + m->location, NREGS);
        m->dataStack->push( m->reg[regNum] );
        break;}
      case STORE:
      { int regNum = mapToRange( m->dataStack->pop() + m->location, NREGS);
        m->reg[regNum] = m->dataStack->pop();
        break;}
        
      case PUSH:
      { m->IP++;
        if (m->IP >= MEMSIZE) m->IP -= MEMSIZE;
        m->dataStack->push( memory[m->IP] );
        break;}
      case POP:
        m->dataStack->pop();
        break;
        
      case INC:
        m->dataStack->push( m->dataStack->pop() + 1 );
        break;
      case DEC:
        m->dataStack->push( m->dataStack->pop() - 1 );
        break;
        
      case ALU:
        {
          func op = static_cast<func>(m->dataStack->pop());
          switch(op) {
            case ADD:
              m->dataStack->push( 
                  m->dataStack->pop() + m->dataStack->pop() );
              break;
            case SUB:
              m->dataStack->push( 
                  m->dataStack->pop() - m->dataStack->pop() );
              break;
            case DIV:
            { int a = m->dataStack->pop();
              int b = m->dataStack->pop();
              if (b == 0) {
                m->dataStack->push(0);
                throw ExecutionError();
              }
              m->dataStack->push( a / b );
              break;}
            case MUL:
              m->dataStack->push( 
                  m->dataStack->pop() * m->dataStack->pop() );
              break;
              
            case GRE:
              m->dataStack->push( 
                  m->dataStack->pop() > m->dataStack->pop() );
              break;
            case LES:
              m->dataStack->push( 
                  m->dataStack->pop() < m->dataStack->pop() );
              break;
            case EQU:
              m->dataStack->push( 
                  m->dataStack->pop() == m->dataStack->pop() );
              break;
               
            case AND:
              m->dataStack->push( 
                  m->dataStack->pop() & m->dataStack->pop() );
              break;
            case OR:
              m->dataStack->push( 
                  m->dataStack->pop() | m->dataStack->pop() );
              break;
            case XOR:
              m->dataStack->push( 
                  m->dataStack->pop() ^ m->dataStack->pop() );
              break;
            default:
              break;
          }
          break;
        }
      
      case RAND:
        m->dataStack->push(rand());
        break;
        
      default:
        break;
    }
  } catch (StackUnderflow) {
    //std::cout << "StackUnderError\n";
    return 1;
  } catch (StackOverflow) {
    //std::cout << "StackOverError\n";
    return 2;
  } catch (ExecutionError) {
    //std::cout << "GeneralError\n";
    return 3;
  }
  return 0;
}

// **************************************************************** //
// Generation of seed Machine
// Return length of Machine

int generatePrimeval() {
  int i = 0;
  /*
    // Length measure loop
      // r0 = 1 (my length)
      PUSH 1 PUSH 0 STORE
      
      DO (16-37), escape after 2142 steps
        // r0++
        PUSH 0 LOAD INC PUSH 0 STORE
        // if instr at r0 and before r0 are NOP, don't loop
        PUSH 0 LOAD     READ PUSH NOP PUSH SUB ALU
        PUSH 0 LOAD DEC READ PUSH NOP PUSH SUB ALU
        PUSH OR ALU SEZ
      LOOP
      // r0++
      PUSH 0 LOAD DEC PUSH 0 STORE
      
      
    // Minelaying loop
      // r1 = -5 (location to copy to)
      PUSH -5 PUSH 1 STORE
      DO
        // copy 5 forks before me, to try and kill anyone approaching
        // copy a FORK to here, pop off success/fail
        PUSH FORK PUSH 1 LOAD WRITE POP
        // r1++
        PUSH 1 LOAD INC PUSH 1 STORE
        // loop if r1<0
        PUSH 1 LOAD SEZ
      LOOP
    
  // main loop
    DO
      
      // MAL loop
        DO
          // r1 =  RAND (location of child)
          RAND PUSH 1 STORE
          // try and MAL here
          PUSH 0 LOAD PUSH 1 LOAD MAL
          // if fail (MAL returned 0), loop
          DEC SEZ
        LOOP
      
      // Copy loop
        //r2 = 0 (instruction to copy)
        PUSH 0 PUSH 2 STORE
        
        // r3 = r0
        PUSH 0 LOAD PUSH 3 STORE
        DO
          // copy from r2 to r1, pop off success/fail of COPY
          PUSH 2 PUSH 1 COPY POP
          // r0--
          PUSH 0 LOAD DEC PUSH 0 STORE
          // r1++
          PUSH 1 LOAD INC PUSH 1 STORE
          // r2++
          PUSH 2 LOAD INC PUSH 2 STORE
          // don't loop if r0=0
          PUSH 0 LOAD SEZ
        LOOP
        
      // Fork child, pop off success/fail
        FORK POP
    LOOP
  
  // end markers
    NOP
    NOP
  */
  
  memory[i++] = PUSH; 
  memory[i++] = 1 ;
  memory[i++] = PUSH; 
  memory[i++] = 0 ;
  memory[i++] = STORE; 
      
  memory[i++] = DO;
  memory[i++] = PUSH; 
  memory[i++] = 0 ;
  memory[i++] = LOAD ;
  memory[i++] = INC ; 
  memory[i++] = PUSH; 
  memory[i++] = 0 ;
  memory[i++] = STORE;
  
  memory[i++] = PUSH; 
  memory[i++] = 0 ; 
  memory[i++] = LOAD  ;   
  memory[i++] = READ ;
  memory[i++] = PUSH ;
  memory[i++] = NOP ;
  memory[i++] = PUSH ; 
  memory[i++] = SUB ;
  memory[i++] = ALU;
  
  memory[i++] = PUSH; 
  memory[i++] = 0 ;
  memory[i++] = LOAD ; 
  memory[i++] = DEC ;
  memory[i++] = READ ;
  memory[i++] = PUSH ;
  memory[i++] = NOP ;
  memory[i++] = PUSH ; 
  memory[i++] = SUB ;
  memory[i++] = ALU;
  
  memory[i++] = PUSH; 
  memory[i++] = OR ;
  memory[i++] = ALU ; 
  memory[i++] = SEZ;
  
  memory[i++] = LOOP;
  
  // r0++
  memory[i++] = PUSH;
  memory[i++] = 0 ;
  memory[i++] = LOAD ;
  memory[i++] = INC ;
  memory[i++] = PUSH; 
  memory[i++] = 0 ;
  memory[i++] = STORE;
  
    // Minelaying loop
      // r1 = -5 (location to write FORK to)
  memory[i++] = PUSH;
  memory[i++] = -5;
  memory[i++] = PUSH;
  memory[i++] = 1;
  memory[i++] = STORE;
  
  memory[i++] = DO;
      // copy a FORK to r1, pop off success/fail
  memory[i++] = PUSH;
  memory[i++] = FORK ;
  memory[i++] = PUSH; 
  memory[i++] = 1 ;
  memory[i++] = LOAD ;
  memory[i++] = WRITE;
  memory[i++] = POP;
      // r1++
  memory[i++] = PUSH ;
  memory[i++] = 1 ;
  memory[i++] = LOAD ;
  memory[i++] = INC ;
  memory[i++] = PUSH;
  memory[i++] = 1 ;
  memory[i++] = STORE;
      // loop if r1>0
  memory[i++] = PUSH ;
  memory[i++] = 1 ;
  memory[i++] = LOAD; 
  memory[i++] = SEZ;
  
  memory[i++] = LOOP;
  
  // main loop   
  memory[i++] = DO;
  
  // MAL loop
  memory[i++] = DO;
  
  memory[i++] = RAND;
  memory[i++] = PUSH; 
  memory[i++] = 1 ;
  memory[i++] = STORE;
  
  memory[i++] = PUSH; 
  memory[i++] = 0 ;
  memory[i++] = LOAD ; 
  memory[i++] = PUSH; 
  memory[i++] = 1 ;
  memory[i++] = LOAD; 
  memory[i++] = MAL;
  
  memory[i++] = DEC; 
  memory[i++] = SEZ;
  
  memory[i++] = LOOP;
  
  // r3 = r0
  memory[i++] = PUSH;
  memory[i++] = 0;
  memory[i++] = LOAD;
  memory[i++] = PUSH;
  memory[i++] = 3;
  memory[i++] = STORE;
  //r2=0
  memory[i++] = PUSH; 
  memory[i++] = 0 ;
  memory[i++] = PUSH; 
  memory[i++] = 2 ;
  memory[i++] = STORE;
      
  memory[i++] = DO;
  //copy
  memory[i++] = PUSH; 
  memory[i++] = 2 ; 
  memory[i++] = LOAD ; 
  memory[i++] = PUSH ;
  memory[i++] = 1 ;
  memory[i++] = LOAD ;
  memory[i++] = COPY;  
  memory[i++] = POP;
  // r3--
  memory[i++] = PUSH;
  memory[i++] = 3 ;
  memory[i++] = LOAD ;
  memory[i++] = DEC ;
  memory[i++] = PUSH; 
  memory[i++] = 3 ;
  memory[i++] = STORE;
  // r1++
  memory[i++] = PUSH; 
  memory[i++] = 1 ;
  memory[i++] = LOAD;
  memory[i++] = INC ;
  memory[i++] = PUSH; 
  memory[i++] = 1 ;
  memory[i++] = STORE;
  // r2++
  memory[i++] = PUSH; 
  memory[i++] = 2 ;
  memory[i++] = LOAD ;
  memory[i++] = INC ;
  memory[i++] = PUSH; 
  memory[i++] = 2 ;
  memory[i++] = STORE;
  // don't loop if r3=0
  memory[i++] = PUSH; 
  memory[i++] = 3;
  memory[i++] = LOAD;
  memory[i++] = SEZ;
  
  memory[i++] = LOOP; 
      
  // Fork child, pop off success/fail
  memory[i++] = FORK;
  memory[i++] = POP;
  
  memory[i++] = LOOP;
 
  // end markers
  memory[i++] = NOP;
  memory[i++] = NOP; 
  
  return i;
}

// **************************************************************** //
// Initialisation of world
// Generate seed and give it a CPU

void initialise() {
  int i = generatePrimeval();
  Machine* m = new Machine(0, i);
  CPUs->enqueue(m);
  memAlloc(0, i, m);
}

// **************************************************************** //
// Display memory to stdout
// Shows memory protection, memory contents and Machine locations

void printMemory() {
  node<Machine*>* current = CPUs->getHead();
  
  bool CPUpresent[MEMSIZE];
  int i;
  for (i=0; i < MEMSIZE; i++)
    CPUpresent[i] = 0;
  
  std::cout << "  IPs: ";
  while (current != NULL) {
    CPUpresent[current->val->IP] = true;
    std::cout << current->val->IP << ",";
    current = current->next;
  }
  std::cout << "\n";
  
  for (i=0; i < MEMSIZE; i++) {
      // new line
      if (i % 5 == 0) std::cout << "\n" << std::left << std::setw(10) << i;
      
      // memory protection
      if (memProtect[i] != NULL) 
        std::cout << std::right << std::setw(9) << memProtect[i];
      else 
        std::cout << "         ";
      
      // active cpu here
      if (CPUpresent[i]) std::cout << "->";
      else std::cout << "  ";
      
      // instruction
      if ((i > 0) && (memory[i-1] == PUSH) && (i < 1 || memory[i-2] != PUSH))
        std::cout << std::left << std::setw(5) << (int)memory[i];
      else {
        switch (static_cast<instr>(memory[i])) {
          case NOP:   std::cout << "     "; break;
          case MAL:   std::cout << "MAL  "; break;
          case FORK:  std::cout << "FORK "; break;
          case COPY:  std::cout << "COPY "; break;
          case WRITE: std::cout << "WRITE"; break;
          case READ:  std::cout << "READ "; break;
          case DO:    std::cout << "DO   "; break;
          case LOOP:  std::cout << "LOOP "; break;
          case SLTZ:  std::cout << "SLTZ "; break;
          case SEZ:   std::cout << "SEZ  "; break;
          case LOAD:  std::cout << "LOAD "; break;
          case STORE: std::cout << "STORE"; break;
          case PUSH:  std::cout << "PUSH "; break;
          case POP:   std::cout << "POP  "; break;
          case INC:   std::cout << "INC  "; break;
          case DEC:   std::cout << "DEC  "; break;
          case ALU:   std::cout << "ALU  "; break;
          case RAND:  std::cout << "RAND "; break;
          default: 
            std::cout << std::left << std::setw(5) << (int)memory[i]; break;
        }
      } 
      std::cout << " ";
  }
  std::cout << "\n";
}

// **************************************************************** //
// Display number of Machines of different lengths

void printCPUInfo() {
  // print CPUs of each length
  int num[500];
  int i;
  for (i=0; i<500; i++) 
    num[i] = 0;
    
  node<Machine*>* current = CPUs->getHead();
  while (current != NULL) {
    num[current->val->mySize]++;
    current = current->next;
  }
  
  std::cout << "  CPUs of:\n";
  for (i=0; i<500; i++)
    if (num[i] > 0) std::cout << "    Size " << i << ": " << num[i] << "\n";
}

// **************************************************************** //
// Print array contents

void printArray(short int array[], int len) {
  int i;
  for (i=0; i < len; i++)
    std::cout << array[i] << ",";
  std::cout << "\n";
}

// **************************************************************** //
//                Setup memory and run simulation
// **************************************************************** //

int main() {
  //redirect std::cout to out.txt
  std::ofstream out("out.txt");
  std::cout.rdbuf(out.rdbuf());
  
  int i;
  for (i=0; i < MEMSIZE; i++) 
    memProtect[i] = NULL;

  // print general information
  std::cout << "Settings:\n";
  std::cout << "  Memory size     : " << MEMSIZE << "\n";
  std::cout << "  Simulation steps: " << SIMSTEPS << "\n";
  std::cout << "  Print intervals : " << PRINTINFOTIME << "\n";
  std::cout << "  Min free % mem  : " << MINFREEMEM << "\n";
  std::cout << "\n";
  std::cout << "  Max programs    : " << MAXALIVE << "\n";
  std::cout << "  Program size    : " << MINSIZE << "-" << MAXSIZE << "\n";
  std::cout << "  Iterations/step : " << STEPSPERCYCLE << "\n";
  std::cout << "  Iter lost/error : " << ERRORSTEPS << "\n";
  std::cout << "  Loopstack size  : " << LOOPSTACKSIZE << "\n";
  std::cout << "  Datastack size  : " << DATASTACKSIZE << "\n";
  std::cout << "  Number registers: " << NREGS << "\n";
  std::cout << "\n";
  std::cout << "  Copy fault chance     : 1/" << MUTCHANCE << "\n";
  std::cout << "  Execution fault chance: 1/" << ERRORCHANCE << "\n";
  std::cout << "\n";
  // seed RNG
  {
    int seed = time(NULL);
    std::cout << "  Seed: " << seed << "\n";
    srand(seed);
  }
  
  // add primeval
  initialise();
  
  int numAlive, iters;
  for (iters=0; iters <= SIMSTEPS; iters++) {
  
    // printing interesting info
    if (iters % PRINTINFOTIME == 0) {
      std::cout << "\n########################################\n";
      std::cout << "GLOBAL STEP " << iters << "\n";
      //std::cout << "Active: " << numAlive << "\n";
      printCPUInfo();
      printMemory();
    }
    numAlive = 0;
    // executing machines
    node<Machine*>* current = CPUs->getHead();
    while (current != NULL && numAlive < MAXALIVE) {
      Machine* m = current->val;
      assert(m != NULL);
      // execute CPU
      numAlive++;
      //std::cout << "\n**********\n";
      //std::cout << "\nEcecuting CPU " << m << "\n";
      int i; bool error = false;
      for (i=0; i < STEPSPERCYCLE; i++) {
        /*std::cout << "IP: " << m->IP << "\n";
        std::cout << "Instruction: " << (int)memory[m->IP] << "\n";
        std::cout << "Datastack: "; m->dataStack->printStack();
        std::cout << "Loopstack: "; m->loopStack->printStack();
        std::cout << "Registers: "; printArray(m->reg, NREGS);*/
        
        assert(m->IP >= 0 && m->IP < MEMSIZE);
        if (execute(m)) error = true;
        assert(m->IP >= 0 && m->IP < MEMSIZE);
        
        m->IP++;
        if (m->IP >= MEMSIZE) m->IP -= MEMSIZE;
        
        // if an error occured, ie execute returned non-zero
        // promote in CPUs queue (so killed earlier)
        // and reduce steps left
        if (error) {
          CPUs->promote(current);
          i += ERRORSTEPS;
        }
      }
      current = current->next;
    }
    
    // freeing memory when not much free or too many Machines
    while (memAvailable() < (MEMSIZE*MINFREEMEM) || numAlive >= MAXALIVE) {
      killCPU();
      numAlive--;
    }
  }
  // finish without error
  return 0;
}
