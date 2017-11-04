
#include <limits.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "regs.h"
#include "memory.h"
#include "loader.h"
#include "syscall.h"
#include "dlite.h"
#include "options.h"
#include "stats.h"
#include "sim.h"
#include "decode.def"

#include "instr.h"

/* PARAMETERS OF THE TOMASULO'S ALGORITHM */

#define INSTR_QUEUE_SIZE         10

#define RESERV_INT_SIZE    4
#define RESERV_FP_SIZE     2
#define FU_INT_SIZE        2
#define FU_FP_SIZE         1

#define FU_INT_LATENCY     4
#define FU_FP_LATENCY      9

/* IDENTIFYING INSTRUCTIONS */

//unconditional branch, jump or call
#define IS_UNCOND_CTRL(op) (MD_OP_FLAGS(op) & F_CALL || \
                         MD_OP_FLAGS(op) & F_UNCOND)

//conditional branch instruction
#define IS_COND_CTRL(op) (MD_OP_FLAGS(op) & F_COND)

//floating-point computation
#define IS_FCOMP(op) (MD_OP_FLAGS(op) & F_FCOMP)

//integer computation
#define IS_ICOMP(op) (MD_OP_FLAGS(op) & F_ICOMP)

//load instruction
#define IS_LOAD(op)  (MD_OP_FLAGS(op) & F_LOAD)

//store instruction
#define IS_STORE(op) (MD_OP_FLAGS(op) & F_STORE)

//trap instruction
#define IS_TRAP(op) (MD_OP_FLAGS(op) & F_TRAP) 

#define USES_INT_FU(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_STORE(op))
#define USES_FP_FU(op) (IS_FCOMP(op))

#define WRITES_CDB(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_FCOMP(op))

/* FOR DEBUGGING */

//prints info about an instruction
#define PRINT_INST(out,instr,str,cycle)	\
  myfprintf(out, "%d: %s", cycle, str);		\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

#define PRINT_REG(out,reg,str,instr) \
  myfprintf(out, "reg#%d %s ", reg, str);	\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

/* VARIABLES */

static int doneCount = 0;

//instruction queue for tomasulo
static instruction_t* instr_queue[INSTR_QUEUE_SIZE];
//number of instructions in the instruction queue
static int instr_queue_size = 0;
static int ifq_head = 0;
static int ifq_tail = 0;

//reservation stations (each reservation station entry contains a pointer to an instruction)
static instruction_t* reservINT[RESERV_INT_SIZE];
static instruction_t* reservFP[RESERV_FP_SIZE];

//functional units
static instruction_t* fuINT[FU_INT_SIZE];
static instruction_t* fuFP[FU_FP_SIZE];

//common data bus
static instruction_t* commonDataBus = NULL;

//The map table keeps track of which instruction produces the value for each register
static instruction_t* map_table[MD_TOTAL_REGS];

//the index of the last instruction fetched
static int fetch_index = 0;

/* FUNCTIONAL UNITS */


/* RESERVATION STATIONS */


/* 
 * Description: 
 * 	Checks if simulation is done by finishing the very last instruction
 *      Remember that simulation is done only if the entire pipeline is empty
 * Inputs:
 * 	sim_insn: the total number of instructions simulated
 * Returns:
 * 	True: if simulation is finished
 */
static bool is_simulation_done(counter_t sim_insn) {

  return doneCount == sim_insn;
}

/* 
 * Description: 
 * 	Retires the instruction from writing to the Common Data Bus
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void CDB_To_retire(int current_cycle) {

  if (commonDataBus) {
    for (int i = 0; i < 2; i++) {
      if (map_table[commonDataBus->r_out[i]] == commonDataBus) {
        map_table[commonDataBus->r_out[i]] = NULL;
      }
    }
		for (int i = 0; i < RESERV_INT_SIZE; i++) {
			for (int j = 0; j < 3; j++) {
				if (reservINT[i]!=NULL && reservINT[i]->Q[j]!= NULL && reservINT[i]->Q[j] == commonDataBus) {
					reservINT[i]->Q[j] = NULL;
				}
			}
		}
		for (int i = 0; i < RESERV_FP_SIZE; i++) {
			for (int j = 0; j < 3; j++) {
				if (reservFP[i]!=NULL && reservFP[i]->Q[j]!= NULL && reservFP[i]->Q[j] == commonDataBus) {
					reservFP[i]->Q[j] = NULL;
				}
			}
		}
    commonDataBus = NULL;
    doneCount++;
  }
}

void free_stations(instruction_t *instr) {
  if (USES_INT_FU(instr->op)) {
    for (int i = 0; i < FU_INT_SIZE; i++) {
      if (fuINT[i] == instr) {
        fuINT[i] = NULL;
        break;
      }
    }
    for (int i = 0; i < RESERV_INT_SIZE; i++) {
      if (reservINT[i] == instr) {
        reservINT[i] = NULL;
        break;
      }
    }
  } else if (USES_FP_FU(instr->op)) {
    for (int i = 0; i < FU_FP_SIZE; i++) {
      if (fuFP[i] == instr) {
        fuFP[i] = NULL;
        break;
      }
    }
    for (int i = 0; i < RESERV_FP_SIZE; i++) {
      if (reservFP[i] == instr) {
        reservFP[i] = NULL;
        break;
      }
    }
  } else {
    printf("Error: instruction not recognized\n");
    assert(false);
  }
}


/* 
 * Description: 
 * 	Moves an instruction from the execution stage to common data bus (if possible)
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void execute_To_CDB(int current_cycle) {

  int oldest = -1;
  instruction_t *oldest_instr = NULL;
  
  for (int i = 0; i < FU_INT_SIZE; i++) {
    if (fuINT[i] && current_cycle >= fuINT[i]->tom_execute_cycle + FU_INT_LATENCY) {
      if (IS_STORE(fuINT[i]->op)) {
        free_stations(fuINT[i]);
        doneCount++;
      }
			else if (oldest == -1 || fuINT[i]->index < oldest) {
        oldest = fuINT[i]->index;
        oldest_instr = fuINT[i];
      }
    }
  }
  if (fuFP[0] && current_cycle >= fuFP[0]->tom_execute_cycle + FU_FP_LATENCY) {
    if (oldest == -1 || fuFP[0]->index < oldest) {
      oldest = fuFP[0]->index;
      oldest_instr = fuFP[0];
    }
  }
  
  if (oldest_instr) {
    oldest_instr->tom_cdb_cycle = current_cycle;
    free_stations(oldest_instr);
    commonDataBus = oldest_instr;
  }

}

/* 
 * Description: 
 * 	Moves instruction(s) from the issue to the execute stage (if possible). We prioritize old instructions
 *      (in program order) over new ones, if they both contend for the same functional unit.
 *      All RAW dependences need to have been resolved with stalls before an instruction enters execute.
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void issue_To_execute(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
	for (int i=0; i<FU_INT_SIZE; i++) {
		if (fuINT[i] == NULL) {
			//function unit is available
			bool found = false;
			int j = 0;
	    int oldest_rs_int = -1;
			while (j < RESERV_INT_SIZE) {
			//Find an int instruction that is not executed yet and is ready to be executed
				if(reservINT[j]!=NULL && reservINT[j]->tom_execute_cycle==0 && reservINT[j]->Q[0]==NULL && reservINT[j]->Q[1]==NULL && reservINT[j]->Q[2]==NULL) {
					if (!found) {
						oldest_rs_int = j;
						found = true;
					}
					else if (reservINT[j]->index<reservINT[oldest_rs_int]->index) {
						oldest_rs_int = j;
					}
				}
				j++;	
			}
			if (found) {
				reservINT[oldest_rs_int]->tom_execute_cycle = current_cycle;
			  fuINT[i] = reservINT[oldest_rs_int];
			}
		}
	}				
	for (int i=0; i<FU_FP_SIZE; i++) {
		if (fuFP[i] == NULL) {
			//function unit is available
			bool found = false;
			int j = 0;
	    int oldest_rs_fp = -1;
			while (j < RESERV_FP_SIZE) {
			//Find an int instruction that is not executed yet and is ready to be executed
				if(reservFP[j]!=NULL && reservFP[j]->tom_execute_cycle==0 && reservFP[j]->Q[0]==NULL && reservFP[j]->Q[1]==NULL && reservFP[j]->Q[2]==NULL) {
					if (!found) {
						oldest_rs_fp = j;
						found = true;
					}
					else if (reservFP[j]->tom_dispatch_cycle<=reservFP[oldest_rs_fp]->tom_dispatch_cycle) {
						oldest_rs_fp = j;
					}
				}
				j++;	
			}
			if (found) {
				reservFP[oldest_rs_fp]->tom_execute_cycle = current_cycle;
			 	fuFP[i] = reservFP[oldest_rs_fp];	
			}
		}
	}				
}

void map_operands(instruction_t* instr) {
  for (int i = 0; i < 3; i++) {
    if (instr->r_in[i] != DNA) {
      instr->Q[i] = map_table[instr->r_in[i]];
    }
  }
  for (int i = 0; i < 2; i++) {
    if (instr->r_out[i] != DNA) {
      map_table[instr->r_out[i]] = instr;
    }
  }
}

/* 
 * Description: 
 * 	Moves instruction(s) from the dispatch stage to the issue stage
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void dispatch_To_issue(int current_cycle) {
  if(instr_queue_size > 0) {
    instruction_t* head_instr = instr_queue[ifq_head];
    enum md_opcode op = head_instr->op;
    if (IS_UNCOND_CTRL(op) || IS_COND_CTRL(op)) {
      ifq_head = (ifq_head + 1) % INSTR_QUEUE_SIZE;
      instr_queue_size--;
      doneCount++;
      
    } else if (USES_FP_FU(op)) {
      for (int i = 0; i < RESERV_FP_SIZE; i++) {
        if (reservFP[i] == NULL) {
          reservFP[i] = head_instr;
          head_instr->tom_issue_cycle = current_cycle;
          ifq_head = (ifq_head + 1) % INSTR_QUEUE_SIZE;
          instr_queue_size--;
          map_operands(head_instr);
					break;
        }
      }
      
    } else if (USES_INT_FU(op)) {
      for (int i = 0; i < RESERV_INT_SIZE; i++) {
        if (reservINT[i] == NULL) {
          reservINT[i] = head_instr;
          head_instr->tom_issue_cycle = current_cycle;
          ifq_head = (ifq_head + 1) % INSTR_QUEUE_SIZE;
          instr_queue_size--;
          map_operands(head_instr);
					break;
        }
      }
      
    } else {
      //unrecognized instruction
      printf("Unrecognized instruction\n");
      assert(false);
    }

  }
}

/* 
 * Description: 
 * 	Grabs an instruction from the instruction trace (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	None
 */
void fetch(instruction_trace_t* trace) {
  instruction_t* new_instr;
  do {
    fetch_index++;
    new_instr = get_instr(trace, fetch_index);
    if (IS_TRAP(new_instr->op)) {
      doneCount++;
    }
  } while (IS_TRAP(new_instr->op));

  instr_queue[ifq_tail] = new_instr;
}

/* 
 * Description: 
 * 	Calls fetch and dispatches an instruction at the same cycle (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void fetch_To_dispatch(instruction_trace_t* trace, int current_cycle) {
  if (instr_queue_size < INSTR_QUEUE_SIZE && fetch_index < sim_num_insn) {
    fetch(trace);
    instr_queue[ifq_tail]->tom_dispatch_cycle = current_cycle;
    ifq_tail = (ifq_tail+1) % INSTR_QUEUE_SIZE;
    instr_queue_size++;
  }
}

/* 
 * Description: 
 * 	Performs a cycle-by-cycle simulation of the 4-stage pipeline
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	The total number of cycles it takes to execute the instructions.
 * Extra Notes:
 * 	sim_num_insn: the number of instructions in the trace
 */
counter_t runTomasulo(instruction_trace_t* trace)
{
  instruction_t* table = trace->table;
  //initialize instruction queue
  int i;
  for (i = 0; i < INSTR_QUEUE_SIZE; i++) {
    instr_queue[i] = NULL;
  }

  //initialize reservation stations
  for (i = 0; i < RESERV_INT_SIZE; i++) {
      reservINT[i] = NULL;
  }

  for(i = 0; i < RESERV_FP_SIZE; i++) {
      reservFP[i] = NULL;
  }

  //initialize functional units
  for (i = 0; i < FU_INT_SIZE; i++) {
    fuINT[i] = NULL;
  }

  for (i = 0; i < FU_FP_SIZE; i++) {
    fuFP[i] = NULL;
  }

  //initialize map_table to no producers
  int reg;
  for (reg = 0; reg < MD_TOTAL_REGS; reg++) {
    map_table[reg] = NULL;
  }
  int cycle = 1;  
  while (true) {
     /* ECE552: YOUR CODE GOES HERE */
		CDB_To_retire(cycle);
		execute_To_CDB(cycle);
		issue_To_execute(cycle);
		dispatch_To_issue(cycle);
		fetch_To_dispatch(trace,cycle);
		cycle++;
		
    if (is_simulation_done(sim_num_insn))
      break;
	}
  
  return cycle;
}
