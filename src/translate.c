/* This project is based on the MIPS Assembler of CS61C in UC Berkeley.
   The framework of this project is been modified to be suitable for RISC-V
   in CS110 course in ShanghaiTech University by Zhijie Yang in March 2019.
   Updated by Chibin Zhang and Zhe Ye in March 2021.
*/

#include "translate.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "block.h"
#include "tables.h"
#include "translate_utils.h"


static const PseudoHandler pseudo_handlers[] = {
    {"beqz", transform_beqz}, {"bnez", transform_bnez}, {"li", transform_li},
    {"mv", transform_mv},     {"j", transform_j},       {"jr", transform_jr},
    {"jal", transform_jal},   {"jalr", transform_jalr}, {"lw", transform_lw},
};

/* 
Fields per entry:
  - const char* name;         -- instr name
  - InstrType instr_type;     -- instr format, e.g. R_type
  - uint8_t opcode;
  - uint8_t funct3;
  - uint8_t funct7;           -- funct7 or partial imm
  - ImmType imm_type;         -- imm type (see translate_utils.h)
*/
static const InstrInfo instr_table[] = {
    // R-type instructions
    {"add", R_TYPE, 0x33, 0x0, 0x00, IMM_NONE},

    {"sub", R_TYPE, 0x33, 0x0, 0x20, IMM_NONE},
    {"xor", R_TYPE, 0x33, 0x4, 0x00, IMM_NONE},
    {"or", R_TYPE, 0x33, 0x6, 0x00, IMM_NONE},
    {"and", R_TYPE, 0x33, 0x7, 0x00, IMM_NONE},
    {"sll", R_TYPE, 0x33, 0x1, 0x00, IMM_NONE},
    {"srl", R_TYPE, 0x33, 0x5, 0x00, IMM_NONE},
    {"sra", R_TYPE, 0x33, 0x5, 0x20, IMM_NONE},
    {"slt", R_TYPE, 0x33, 0x2, 0x00, IMM_NONE},
    {"sltu", R_TYPE, 0x33, 0x3, 0x00, IMM_NONE},
    {"mul", R_TYPE, 0x33, 0x0, 0x01, IMM_NONE},
    {"mulh", R_TYPE, 0x33, 0x1, 0x01, IMM_NONE},
    {"div", R_TYPE, 0x33, 0x4, 0x01, IMM_NONE},
    {"rem", R_TYPE, 0x33, 0x6, 0x01, IMM_NONE},

    // I-type instructions
    {"addi", I_TYPE, 0x13, 0x0, 0x00, IMM_12_SIGNED},
    {"xori", I_TYPE, 0x13, 0x4, 0x00, IMM_12_SIGNED},
    {"ori", I_TYPE, 0x13, 0x6, 0x00, IMM_12_SIGNED},
    {"andi", I_TYPE, 0x13, 0x7, 0x00, IMM_12_SIGNED},
    {"slli", I_TYPE, 0x13, 0x1, 0x00, IMM_5_UNSIGNED},
    {"srli", I_TYPE, 0x13, 0x5, 0x00, IMM_5_UNSIGNED},
    {"srai", I_TYPE, 0x13, 0x5, 0x20, IMM_5_UNSIGNED},
    {"slti", I_TYPE, 0x13, 0x2, 0x00, IMM_12_SIGNED},
    {"sltiu", I_TYPE, 0x13, 0x3, 0x00, IMM_12_SIGNED},
    {"lb", I_TYPE, 0x03, 0x0, 0x00, IMM_12_SIGNED},
    {"lh", I_TYPE, 0x03, 0x1, 0x00, IMM_12_SIGNED},
    {"lw", I_TYPE, 0x03, 0x2, 0x00, IMM_12_SIGNED},
    {"lbu", I_TYPE, 0x03, 0x4, 0x00, IMM_12_SIGNED},
    {"lhu", I_TYPE, 0x03, 0x5, 0x00, IMM_12_SIGNED},
    {"jalr", I_TYPE, 0x67, 0x0, 0x00, IMM_12_SIGNED},
    {"ecall", I_TYPE, 0x73, 0x0, 0x00, IMM_NONE},

    // S-type instructions
    {"sb", S_TYPE, 0x23, 0x0, 0x00, IMM_12_SIGNED},
    {"sh", S_TYPE, 0x23, 0x1, 0x00, IMM_12_SIGNED},
    {"sw", S_TYPE, 0x23, 0x2, 0x00, IMM_12_SIGNED},

    // SB-type instructions
    {"beq", SB_TYPE, 0x63, 0x0, 0x00, IMM_13_SIGNED},
    {"bne", SB_TYPE, 0x63, 0x1, 0x00, IMM_13_SIGNED},
    {"blt", SB_TYPE, 0x63, 0x4, 0x00, IMM_13_SIGNED},
    {"bge", SB_TYPE, 0x63, 0x5, 0x00, IMM_13_SIGNED},
    {"bltu", SB_TYPE, 0x63, 0x6, 0x00, IMM_13_SIGNED},
    {"bgeu", SB_TYPE, 0x63, 0x7, 0x00, IMM_13_SIGNED},

    // U-type instructions
    {"lui", U_TYPE, 0x37, 0x0, 0x00, IMM_20_UNSIGNED},
    {"auipc", U_TYPE, 0x17, 0x0, 0x00, IMM_20_UNSIGNED},

    // UJ-type instructions
    {"jal", UJ_TYPE, 0x6f, 0x0, 0x00, IMM_21_SIGNED},
};

// You need to implement the following functions to expand pseudoinstructions and save them in the intermediate representation block:
unsigned transform_beqz(Block* blk, char** args, int num_args) {
  /* IMPLEMENT ME */
  /* === start === */
  // Check the number of arguments
  if (num_args != 2) {
    return 0;
  }
  char* new_args[3];
  new_args[0] = args[0];
  new_args[1] = "x0";
  new_args[2] = args[1];
  if (!new_args[0] || !new_args[1] || !new_args[2]) {
    allocation_failed();
  }
  if (add_to_block(blk, "beq", new_args, 3) == -1) {
    return 0;
  }
  /* === end === */
  return 1;
}

unsigned transform_bnez(Block* blk, char** args, int num_args) {
  /* IMPLEMENT ME */
  /* === start === */
  if (num_args != 2) {
    return 0;
  }
  char* new_args[3];
  new_args[0] = args[0];
  new_args[1] = "x0";
  new_args[2] = args[1];
  if (!new_args[0] || !new_args[1] || !new_args[2]) {
    allocation_failed();
  }
  if (add_to_block(blk, "bne", new_args, 3) == -1) {
    return 0;
  }
  /* === end === */
  return 1;
}

/* Hint:
  - make sure that the number is representable by 32 bits. (Hint: the number
      can be both signed or unsigned).
  - if the immediate can fit in the imm field of an addiu instruction, then
      expand li into a single addi instruction. Otherwise, expand it into
      a lui-addi pair.

  venus has slightly different translation rules for li, and it allows numbers
  larger than the largest 32 bit number to be loaded with li. You should follow
  the above rules if venus behaves differently.
*/
unsigned transform_li(Block* blk, char** args, int num_args) {
  /* IMPLEMENT ME */
  /* === start === */
  if (num_args != 2) {
    return 0;
  }

  char* rd = args[0];
  char* imm_str = args[1];

  long int imm;
  if (translate_num(&imm, imm_str, IMM_32_SIGNED) == -1) {
    return 0;
  }

  if (is_valid_imm(imm, IMM_12_SIGNED)) {
    char* new_args[3];
    new_args[0] = rd;
    new_args[1] = "x0";
    new_args[2] = imm_str;
    if (!new_args[0] || !new_args[1] || !new_args[2]) {
      allocation_failed();
    }
    if (add_to_block(blk, "addi", new_args, 3) == -1) {
      return 0;
    }
    return 1;
  } else {
    printf("%ld\n", imm);
    int32_t hi20 = (int32_t)(((imm + 0x800) >> 12) & 0xFFFFF);  // 确保是 signed
    int32_t lo12 = imm - (hi20 << 12);  // 这里左移后仍是 signed，结果就不会 wrap


    // 构造 hi20 字符串
    char hi_str[32], lo_str[32];
    snprintf(hi_str, sizeof(hi_str), "%d", hi20);
    snprintf(lo_str, sizeof(lo_str), "%d", lo12);

    // lui rd, hi20
    char* lui_args[2];
    lui_args[0] = rd;
    lui_args[1] = hi_str;
    if (!lui_args[0] || !lui_args[1]) allocation_failed();
    if (add_to_block(blk, "lui", lui_args, 2) == -1) return 0;

    // addi rd, rd, lo12
    char* addi_args[3];
    addi_args[0] = rd;
    addi_args[1] = rd;
    addi_args[2] = lo_str;
    if (!addi_args[0] || !addi_args[1] || !addi_args[2]) allocation_failed();
    if (add_to_block(blk, "addi", addi_args, 3) == -1) return 0;

    return 2;
  }

  return 1;
  /* === end === */
}

/* Hint:
  - your expansion should use the fewest number of instructions possible.
 */
unsigned transform_mv(Block* blk, char** args, int num_args) {
  /* IMPLEMENT ME */
  /* === start === */
  if (num_args != 2) {
    return 0;
  }

  char* rd = args[0];
  char* rs = args[1];

  char* new_args[3];
  new_args[0] = rd;
  new_args[1] = rs;
  new_args[2] = "0";
  if (!new_args[0] || !new_args[1] || !new_args[2]) {
    allocation_failed();
  }
  if (add_to_block(blk, "addi", new_args, 3) == -1) {
    return 0;
  }
  /* === end === */
  return 1;
}

unsigned transform_j(Block* blk, char** args, int num_args) {
  /* IMPLEMENT ME */
  /* === start === */
  if (num_args != 1) {
    return 0;
  }

  char* new_args[2];
  new_args[0] = "x0";
  new_args[1] = args[0];
  if (!new_args[0] || !new_args[1]) {
    allocation_failed();
  }
  if (add_to_block(blk, "jal", new_args, 2) == -1) {
    return 0;
  }
  /* === end === */
  return 1;
}

unsigned transform_jr(Block* blk, char** args, int num_args) {
  /* IMPLEMENT ME */
  /* === start === */
  if (num_args != 1) {
    return 0;  // Invalid number of arguments
  }
  
  // jr rs -> jalr x0, rs, 0
  char* new_args[3];
  new_args[0] = "x0";      // Don't save return address
  new_args[1] = args[0];   // Jump to the address in rs
  new_args[2] = "0";       // With 0 offset
  
  if (!new_args[0] || !new_args[1] || !new_args[2]) {
    allocation_failed();
  }
  
  if (add_to_block(blk, "jalr", new_args, 3) == -1) {
    return 0;
  }
  
  return 1;
  /* === end === */
}

/* Hint:
  - Since handler is selected by instruction name, be careful about
    pseudo/regular instruction name collisions
 */
unsigned transform_jal(Block* blk, char** args, int num_args) {
  /* IMPLEMENT ME */
  /* === start === */
  // Handle two different forms of jal:
  // 1. jal label (pseudo) -> jal x1, label (real)
  // 2. jal rd, label (real) -> already in correct format, pass through

  if (num_args == 1) {
    // Form 1: jal label -> jal x1, label
    char* new_args[2];
    new_args[0] = "x1";      // Return address register
    new_args[1] = args[0];   // Target label
    
    if (!new_args[0] || !new_args[1]) {
      allocation_failed();
    }
    
    if (add_to_block(blk, "jal", new_args, 2) == -1) {
      return 0;
    }
    return 1;
  } else if (num_args == 2) {
    // Form 2: jal rd, label -> already in correct format, pass through
    if (add_to_block(blk, "jal", args, 2) == -1) {
      return 0;
    }
    return 1;
  } else {
    return 0;
  }
  /* === end === */
}

/* Hint:
  - Since handler is selected by instruction name, be careful about
    pseudo/regular instruction name collisions
 */
/* Hint:
  - Since handler is selected by instruction name, be careful about
    pseudo/regular instruction name collisions
 */
unsigned transform_jalr(Block* blk, char** args, int num_args) {
  /* IMPLEMENT ME */
  /* === start === */
  // JALR can be called in three forms:
  // 1. jalr rs1 (pseudo) -> jalr x1, rs1, 0
  // 3. jalr rd, rs1, imm (real instruction) -> no transformation needed
  
  if (num_args == 1) {
    // Form 1: jalr rs1 -> jalr x1, rs1, 0
    char* new_args[3];
    new_args[0] = "x1";      // Return address register
    new_args[1] = args[0];   // Source register
    new_args[2] = "0";       // Immediate offset
    
    if (!new_args[0] || !new_args[1] || !new_args[2]) {
      allocation_failed();
    }
    
    if (add_to_block(blk, "jalr", new_args, 3) == -1) {
      return 0;
    }
    return 1;
  }  else if (num_args == 3) {
    // Form 3: jalr rd, rs1, imm (real instruction)
    // This is already the real instruction format, so pass it through
    if (add_to_block(blk, "jalr", args, 3) == -1) {
      return 0;
    }
    return 1;
  }
  else
  {
    // Invalid number of arguments
    return 0;
  }
  /* === end === */
}

/* Hint:
 * - You should transform the lw instruction into auipc + lw for label
 */
unsigned transform_lw(Block* blk, char** args, int num_args) {
  /* IMPLEMENT ME */
  /* === start === */
  //lw x29 2(x30)
  //lw s1 label1
  if (num_args != 2 && num_args != 3) {
    return 0;
  }

  if (num_args == 3) {
    char* new_args[3];
    new_args[0] = args[0];
    new_args[1] = args[1];
    new_args[2] = args[2];
    if (!new_args[0] || !new_args[1] || !new_args[2]) {
      allocation_failed();
    }
    if (add_to_block(blk, "lw", new_args, 3) == -1) {
      return 0;
    }
    return 1;
  }
  else
  {
    //lw s1 label1
    long int imm;
    if (translate_num(&imm, args[1], IMM_12_SIGNED) == -1) {
      // transform label to auipc + lw
      char* rd = args[0];
      char* label = args[1];

      // Step 1: Add auipc instruction
      char* auipc_args[2];
      auipc_args[0] = rd;
      auipc_args[1] = label;
      if (add_to_block(blk, "auipc", auipc_args, 2) == -1) {
        return 0;
      }

      // Step 2: Add lw instruction with lower 12 bits offset
      char* lw_args[2];
      lw_args[0] = rd;
      lw_args[1] = label;
      if (!lw_args[0] || !lw_args[1])
      {
        allocation_failed();
      }
      if (add_to_block(blk, "lw", lw_args, 2) == -1) {
        return 0;
      }

      return 2;

    } else {
      return 0;
    }
  }
  /* === end === */
}

/* Traverse pseudo_handlers table to select corresponding handler by NAME */
const PseudoHandler* find_pseudo_handler(const char* name) {
  for (size_t i = 0; i < sizeof(pseudo_handlers) / sizeof(pseudo_handlers[0]);
       i++) {
    if (strcmp(name, pseudo_handlers[i].name) == 0) {
      return &pseudo_handlers[i];
    }
  }
  return NULL;
}

/* Writes instructions during the assembler's first pass to BLK. The case
   for pseudo-instructions will be handled by handlers, but you need to
   write code to complete these TRANSFORM functions, as well as dealing
   with general instructions. Your pseudoinstruction expansions should not
   have any side effects.

   BLK is the intermediate instruction block you should write to,
   NAME is the name of the instruction, ARGS is an array of the arguments, and
   NUM_ARGS specifies the number of items in ARGS.

   Error checking for regular instructions are done in pass two. However, for
   pseudoinstructions, you must make sure that ARGS contains the correct number
   of arguments. You do NOT need to check whether the registers / label are
   valid, since that will be checked in part two.

   Returns the number of instructions written (so 0 if there were any errors).
 */
unsigned write_pass_one(Block* blk, const char* name, char** args,
                        int num_args) {
  /* Deal with pseudo-instructions */
  const PseudoHandler* handler = find_pseudo_handler(name);
  if (handler) {
    return handler->transform(blk, args, num_args);
  }
  /* What about general instructions? */
  /* IMPLEMENT ME */
  /* === start === */
  if (add_to_block(blk, name, args, num_args) == -1) {
    return 0;
  } else {
    return 1;
  }
  /* === end === */
  return 0;
}

/* Writes the instruction in hexadecimal format to OUTPUT during pass #2.

   NAME is the name of the instruction, ARGS is an array of the arguments, and
   NUM_ARGS specifies the number of items in ARGS.

   The symbol table (SYMTBL) is given for any symbols that need to be resolved
   at this step.

   You must perform error checking on all instructions and make sure that their
   arguments are valid. If an instruction is invalid, you should not write
   anything to OUTPUT but simply return -1. venus may be a useful resource for
   this step.

   All regular instruction information is given at `instr_table`.

   Note the use of helper functions. Consider writing your own! If the function
   definition comes afterwards, you must declare it first (see translate.h).

   Returns 0 on success and -1 on error.
 */
int translate_inst(FILE* output, const char* name, char** args, size_t num_args,
                   uint32_t addr, SymbolTable* symtbl) {
  for (size_t i = 0; i < sizeof(instr_table) / sizeof(instr_table[0]); i++) {
    const InstrInfo* info = &instr_table[i];
    if (strcmp(name, info->name) == 0) {
      switch (info->instr_type) {
        case R_TYPE:
          return write_rtype(output, info, args, num_args);
        case I_TYPE:
          return write_itype(output, info, args, num_args, addr, symtbl);
        case S_TYPE:
          return write_stype(output, info, args, num_args);
        case SB_TYPE:
          return write_sbtype(output, info, args, num_args, addr, symtbl);
        case U_TYPE:
          return write_utype(output, info, args, num_args, addr, symtbl);
        case UJ_TYPE:
          return write_ujtype(output, info, args, num_args, addr, symtbl);
      }
    }
  }
  return -1;
}

/* A helper function for writing most R-type instructions. You should use
   translate_reg() to parse registers and write_inst_hex() to write to
   OUTPUT. Both are defined in translate_utils.h.

   This function is INCOMPLETE. Complete the implementation below. You will
   find bitwise operations to be the cleanest way to complete this function.
 */
int write_rtype(FILE* output, const InstrInfo* info, char** args,
                size_t num_args) {
  /* IMPLEMENT ME */
  /* === start === */
  if (num_args != 3) {
    return -1;
  }

  int rd = translate_reg(args[0]);
  int rs1 = translate_reg(args[1]);
  int rs2 = translate_reg(args[2]);

  if (rd == -1 || rs1 == -1 || rs2 == -1) {
    return -1;
  }

  uint32_t instruction = 0;
  instruction |= info->opcode;  
  instruction |= (rd & 0x1F) << 7;
  instruction |= (info->funct3 & 0x7) << 12;
  instruction |= (rs1 & 0x1F) << 15;
  instruction |= (rs2 & 0x1F) << 20;
  instruction |= (info->funct7 & 0x7F) << 25;

  write_inst_hex(output, instruction);
  /* === end === */
  return 0;
}

/* Hint:
  - Number of ARGS and immediate range of each I_type instruction may
  vary. Refer to RISC-V green card and design proper encoding rules.
  - Some instruction(s) expanded from pseudo ones may has(have) unresolved
  label(s). lw here use 12-bit signed immediate.
  You need to take that special case into consideration. Refer to
  write_sbtype for detailed relative address calculation.
 */

int write_itype(FILE* output, const InstrInfo* info, char** args,
                size_t num_args, uint32_t addr, SymbolTable* symtbl) {
  /* === start === */

  // Handle special case: ecall
  if (strcmp(info->name, "ecall") == 0) {
    if (num_args != 0) return -1;

    uint32_t instruction = 0;
    instruction |= info->opcode;
    instruction |= (info->funct3 & 0x7) << 12;

    write_inst_hex(output, instruction);
    return 0;
  }

  // Handle load instructions: lb/lh/lw/lbu/lhu rd, imm(rs1)
  if (strcmp(info->name, "lb") == 0 || strcmp(info->name, "lh") == 0 ||
      strcmp(info->name, "lw") == 0 || strcmp(info->name, "lbu") == 0 ||
      strcmp(info->name, "lhu") == 0) {
    
    // Check if we have the correct number of arguments
    if (num_args != 2 && num_args != 3) {
      return -1;
    }

    int rd = translate_reg(args[0]);
    if (rd == -1) {
      return -1;
    }

    // Handle the two different forms: lw rd, imm(rs1) or lw rd, label
    if (num_args == 3) {
      // Form: lw rd, imm(rs1)
      int rs1 = translate_reg(args[2]);
      if (rs1 == -1) {
        return -1;
      }

      long int imm;
      if (translate_num(&imm, args[1], info->imm_type) == -1) {
        return -1;
      }

      if (!is_valid_imm(imm, info->imm_type)) {
        return -1;
      }

      uint32_t instruction = 0;
      instruction |= info->opcode;
      instruction |= (rd & 0x1F) << 7;
      instruction |= (info->funct3 & 0x7) << 12;
      instruction |= (rs1 & 0x1F) << 15;
      instruction |= ((uint32_t)(imm & 0xFFF)) << 20;

     // printf("instruction: %x\n", instruction);

      write_inst_hex(output, instruction);
      return 0;

    } else if (num_args == 2) {
      // Form: lw rd, label
      // This is a special case for pseudo expansions where we need to handle a label
      uint32_t symbol_addr;
      if (get_addr_for_symbol(symtbl, args[1]) == -1) {
        return -1;  // Symbol not found
      }
      symbol_addr = get_addr_for_symbol(symtbl, args[1]);
      
      // Calculate the offset for lower 12 bits
      long int imm = (symbol_addr - addr + 4) & 0xFFF;

      // For this special case, we assume rd is also used as the base register
      // This should have been set up by a preceding auipc instruction
      int rs1 = rd;
      
      uint32_t instruction = 0;
      instruction |= info->opcode;
      instruction |= (rd & 0x1F) << 7;
      instruction |= (info->funct3 & 0x7) << 12;
      instruction |= (rs1 & 0x1F) << 15;
      instruction |= (imm & 0xFFF) << 20;
      
      write_inst_hex(output, instruction);
      return 0;
    }
  }

  // Handle jalr rd, rs1, imm
  if (strcmp(info->name, "jalr") == 0) {
    if (num_args != 3) {
      return -1;
    }

    int rd = translate_reg(args[0]);
    int rs1 = translate_reg(args[1]);
    if (rd == -1 || rs1 == -1) {
      return -1;
    }

    long int imm;
    if (translate_num(&imm, args[2], info->imm_type) == -1) {
      return -1;
    }

    if (!is_valid_imm(imm, info->imm_type)) {
      return -1;
    }

    uint32_t instruction = 0;
    instruction |= info->opcode;
    instruction |= (rd & 0x1F) << 7;
    instruction |= (info->funct3 & 0x7) << 12;
    instruction |= (rs1 & 0x1F) << 15;
    instruction |= (imm & 0xFFF) << 20;

    write_inst_hex(output, instruction);
    return 0;
  }

  // Handle regular I-type instructions: addi, xori, ori, etc.
  if (num_args != 3) {
    return -1;
  }

  int rd = translate_reg(args[0]);
  int rs1 = translate_reg(args[1]);
  if (rd == -1 || rs1 == -1) {
    return -1;
  }

  long int imm;
  if (translate_num(&imm, args[2], info->imm_type) == -1) {
    return -1;
  }

  uint32_t instruction = 0;
  instruction |= info->opcode;
  instruction |= (rd & 0x1F) << 7;
  instruction |= (info->funct3 & 0x7) << 12;
  instruction |= (rs1 & 0x1F) << 15;
  
  // For shift instructions with 5-bit immediate (slli, srli, srai)
  if (strcmp(info->name, "slli") == 0 || strcmp(info->name, "srli") == 0 || 
      strcmp(info->name, "srai") == 0) {
    instruction |= (imm & 0x1F) << 20;
    instruction |= (info->funct7 & 0x7F) << 25;
  } else {
    // For regular 12-bit immediate instructions
    instruction |= (imm & 0xFFF) << 20;
  }

  write_inst_hex(output, instruction);
  return 0;
  /* === end === */
}


int write_stype(FILE* output, const InstrInfo* info, char** args,
                size_t num_args) {
  /* IMPLEMENT ME */
  /* === start === */
  if (num_args != 3) {
    return -1;
  }

  // For S-type, args should be: rs2, imm(rs1)
  int rs2 = translate_reg(args[0]);
  int rs1 = translate_reg(args[2]);

  if (rs1 == -1 || rs2 == -1) {
    return -1;
  }

  long int imm;
  if (translate_num(&imm, args[1], info->imm_type) == -1) {
    return -1;
  }

  // For S-type instructions, the immediate is split:
  // imm[11:5] go in bits 31:25
  // imm[4:0] go in bits 11:7
  uint32_t instruction = 0;
  instruction |= info->opcode;                   // Opcode in bits 6:0
  instruction |= ((imm & 0x1F) << 7);            // imm[4:0] in bits 11:7
  instruction |= (info->funct3 & 0x7) << 12;     // funct3 in bits 14:12
  instruction |= (rs1 & 0x1F) << 15;             // rs1 in bits 19:15
  instruction |= (rs2 & 0x1F) << 20;             // rs2 in bits 24:20
  instruction |= ((imm >> 5) & 0x7F) << 25;      // imm[11:5] in bits 31:25

  write_inst_hex(output, instruction);
  /* === end === */
  return 0;
}

/* Hint:
  - the way for branch to calculate relative address. e.g. bne
     bne rs rt label
   assume the byte_offset(addr) of label is L,
   current instruction byte_offset(addr) is A
   the relative address I for label satisfy:
     L = A + I
   so the relative addres is
     I = L - A
*/
int write_sbtype(FILE* output, const InstrInfo* info, char** args,
                 size_t num_args, uint32_t addr, SymbolTable* symtbl) {
  //printf("write_sbtype\n");
  /* IMPLEMENT ME */
  /* === start === */
  // SB-type instructions should have exactly 3 arguments: rs1, rs2, and label/immediate
  if (num_args != 3) {
    return -1;
  }
  
  // Parse the registers
  int rs1 = translate_reg(args[0]);
  int rs2 = translate_reg(args[1]);
  if (rs1 == -1 || rs2 == -1) {
    return -1;  // Invalid registers
  }
  
    // Parse the immediate value or label
  long int imm;
  if (translate_num(&imm, args[2], info->imm_type) == -1) {
    // If not a number, try to resolve as a symbol
    uint32_t symbol_addr;
    if (get_addr_for_symbol(symtbl, args[2]) == -1) {
      return -1;  // Symbol not found
    }
    symbol_addr = get_addr_for_symbol(symtbl, args[2]);
    
    // Calculate relative address for branch
    // L = A + I, so I = L - A
    imm = symbol_addr - addr;
  }

  // Encode the instruction
  uint32_t instruction = 0;
  instruction |= info->opcode;                 // Opcode in bits 0-6
  instruction |= ((imm >> 11) & 0x1) << 7;     // imm[11] -> bit 7
  instruction |= ((imm >> 1) & 0xF) << 8;      // imm[4:1] -> bits 11-8
  instruction |= (info->funct3 & 0x7) << 12;   // funct3 in bits 14-12
  instruction |= (rs1 & 0x1F) << 15;           // rs1 in bits 19-15
  instruction |= (rs2 & 0x1F) << 20;           // rs2 in bits 24-20
  instruction |= ((imm >> 5) & 0x3F) << 25;    // imm[10:5] -> bits 30-25
  instruction |= ((imm >> 12) & 0x1) << 31;    // imm[12] -> bit 31

  // Write the encoded instruction to output
  //printf("instruction: %x\n", instruction);
  write_inst_hex(output, instruction);

  /* === end === */
  return 0;
}

/* Hint:
  - Some instruction(s) expanded from pseudo ones may has(have) unresolved
  label(s). You need to take that special case into consideration. Refer to
  write_sbtype for detailed relative address calculation.
 */
int write_utype(FILE* output, const InstrInfo* info, char** args,
                size_t num_args, uint32_t addr, SymbolTable* symtbl) {
  /* IMPLEMENT ME */
  /* === start === */
  // U-type instructions (lui, auipc) should have exactly 2 arguments: rd and immediate/label
  if (num_args != 2) {
    return -1;
  }
  
  // Parse the destination register
  int rd = translate_reg(args[0]);
  if (rd == -1) {
    return -1;  // Invalid register
  }
  
  // Parse the immediate value or label
  long int imm;
  if (translate_num(&imm, args[1], info->imm_type) == -1) {
    // If not a number, try to resolve as a symbol
    uint32_t symbol_addr;
    if (get_addr_for_symbol(symtbl, args[1]) == -1) {
      return -1;  // Symbol not found
    }
    symbol_addr = get_addr_for_symbol(symtbl, args[1]);
    
    // For U-type instructions like auipc that might use labels
    // We need the upper 20 bits of the address
    if (strcmp(info->name, "auipc") == 0) {
      // Calculate offset from current address
      imm = (symbol_addr - addr + 0x800);
      // For auipc, we need to account for the upper 20 bits
      imm = imm >> 12;
    }
    else
    {
      // For lui, we just take the upper 20 bits of the symbol address
      imm = symbol_addr >> 12;
    }
  }
  
  // For U-type instructions, immediate is the upper 20 bits (imm[31:12])
  
  // Encode the instruction
  uint32_t instruction = 0;
  instruction |= info->opcode;              // Opcode in bits 0-6
  instruction |= (rd & 0x1F) << 7;          // rd in bits 7-11
  instruction |= (imm & 0xFFFFF) << 12;     // imm[31:12] in bits 31-12
  
  // Write the encoded instruction to output
  write_inst_hex(output, instruction);
  /* === end === */
  return 0;
}

/* In this project there is no need to relocate labels,
   you may think about the reasons. */
int write_ujtype(FILE* output, const InstrInfo* info, char** args,
                 size_t num_args, uint32_t addr, SymbolTable* symtbl) {
  /* IMPLEMENT ME */
  /* === start === */
  // UJ-type instructions (jal) should have exactly 2 arguments: rd and immediate/label
  if (num_args != 2) {
    return -1;
  }
  
  // Parse the destination register
  int rd = translate_reg(args[0]);
  if (rd == -1) {
    return -1;  // Invalid register
  }
  
  // Parse the immediate value or label
  long imm1;
  if (translate_num(&imm1, args[1], info->imm_type) == -1) {
    // If not a number, try to resolve as a symbol
    uint32_t symbol_addr;
    if (get_addr_for_symbol(symtbl, args[1]) == -1) {
     // printf("get_addr_fail\n");
      return -1; // Symbol not found
    }
    symbol_addr = get_addr_for_symbol(symtbl, args[1]);
    // Calculate relative address for jump
    // L = A + I, so I = L - 
    imm1 = symbol_addr - addr;
  }
  
  // Check if immediate is within valid range for UJ-type (21-bit signed)
  // and is aligned to 2-byte boundary (even number)


  // UJ-type immediate encoding has a complex bit arrangement:
  // imm[20|10:1|11|19:12] -> bits [31:12]
  unsigned imm = ((unsigned)imm1) & 0x1FFFFF;
  // Encode the instruction
  uint32_t instruction = 0;
  instruction |= info->opcode;                 // Opcode in bits 0-6
  instruction |= (rd & 0x1F) << 7;             // rd in bits 7-11
  instruction |= (((imm >> 12) & 0xFF) << 12); // imm[19:12] -> bits 19-12
  instruction |= (((imm >> 11) & 0x1) << 20);  // imm[11] -> bit 20
  instruction |= (((imm >> 1) & 0x3FF) << 21); // imm[10:1] -> bits 30-21
  instruction |= (((imm >> 20) & 0x1) << 31);  // imm[20] -> bit 31
  
  // Write the encoded instruction to output
  write_inst_hex(output, instruction);
  /* === end === */
  return 0;
}
