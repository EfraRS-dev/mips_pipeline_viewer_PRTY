// src/context/SimulationContext.tsx
"use client"; // Add 'use client' directive

import {
  createContext,
  useCallback,
  useContext,
  useEffect,
  useMemo,
  useRef,
  useState,
  type PropsWithChildren,
} from "react";
import * as React from "react";
import { binaryToHex, hexToBinary, translateInstructionToMIPS } from "./Converter";

// Define the stage names (optional, but good for clarity)
const STAGE_NAMES = ["IF", "ID", "EX", "MEM", "WB"] as const;
type StageName = (typeof STAGE_NAMES)[number];

type InstructionType = "R" | "I" | "J";
type HazardType = "RAW" | "WAW" | "NONE";

interface RegisterUsage {
  rs: number;
  rt: number;
  rd: number;
  opcode: number;
  funct: number;
  type: InstructionType;
  isLoad: boolean;
  isStore: boolean; // Añadido para detectar instrucciones de almacenamiento
}

interface HazardInfo {
  type: HazardType;
  description: string;
  canForward: boolean;
  stallCycles: number;
}

interface ForwardingInfo {
  from: number;
  to: number;
  fromStage: StageName;
  toStage: StageName;
  register: string;
}

// Modificar el regMap para mantener consistencia con $
const regMap: { [key: string]: string } = {
  "0": "zero",
  "1": "at",
  "2": "v0",
  "3": "v1",
  "4": "a0",
  "5": "a1",
  "6": "a2",
  "7": "a3",
  "8": "t0",
  "9": "t1",
  "10": "t2",
  "11": "t3",
  "12": "t4",
  "13": "t5",
  "14": "t6",
  "15": "t7",
  "16": "s0",
  "17": "s1",
  "18": "s2",
  "19": "s3",
  "20": "s4",
  "21": "s5",
  "22": "s6",
  "23": "s7",
  "24": "t8",
  "25": "t9",
  "26": "k0",
  "27": "k1",
  "28": "gp",
  "29": "sp",
  "30": "fp",
  "31": "ra",
};

// Initialize registers and memory (from MIPS.jsx)
const initialRegisters = {
  "$zero": 0, "$at": 0, "$v0": 0, "$v1": 0,
  "$a0": 0, "$a1": 0, "$a2": 0, "$a3": 0,
  "$t0": 0, "$t1": 0, "$t2": 0, "$t3": 0,
  "$t4": 0, "$t5": 0, "$t6": 0, "$t7": 0,
  "$s0": 0, "$s1": 0, "$s2": 0, "$s3": 0,
  "$s4": 0, "$s5": 0, "$s6": 0, "$s7": 0,
  "$t8": 0, "$t9": 0, "$k0": 0, "$k1": 0,
  "$gp": 0, "$sp": 0, "$fp": 0, "$ra": 0,
};

// Mantener la memoria en 32 palabras (direcciones de 0 a 31)
const initialMemory = Array.from({ length: 32 }).reduce<Record<number, number>>(
  (acc, _, i) => {
    acc[i] = 0;
    return acc;
  },
  {} as Record<number, number>
);

interface SimulationState {
  instructions: string[];
  currentCycle: number;
  maxCycles: number;
  isRunning: boolean;
  stageCount: number;
  instructionStages: Record<number, number | null>;
  isFinished: boolean;
  registerUsage: Record<number, RegisterUsage>;
  hazards: Record<number, HazardInfo>;
  forwardings: Record<number, ForwardingInfo[]>;
  stalls: Record<number, number>;
  currentStallCycles: number;
  forwardingEnabled: boolean;
  stallsEnabled: boolean;
  registers: Record<string, number>;
  memory: Record<number, number>;
  PC: number;
}

// Define the shape of the context actions
interface SimulationActions {
  startSimulation: (submittedInstructions: string[]) => void;
  resetSimulation: () => void;
  pauseSimulation: () => void;
  resumeSimulation: () => void;
  setForwardingEnabled: (enabled: boolean) => void;
  setStallsEnabled: (enabled: boolean) => void;
}

// Create the contexts
const SimulationStateContext = createContext<SimulationState | undefined>(undefined);
const SimulationActionsContext = createContext<SimulationActions | undefined>(undefined);

const DEFAULT_STAGE_COUNT = STAGE_NAMES.length; // Use length of defined stages

const initialState: SimulationState = {
  instructions: [],
  currentCycle: 0,
  maxCycles: 0,
  isRunning: false,
  stageCount: DEFAULT_STAGE_COUNT,
  instructionStages: {},
  isFinished: false,
  registerUsage: {},
  hazards: {},
  forwardings: {},
  stalls: {},
  currentStallCycles: 0,
  forwardingEnabled: true,
  stallsEnabled: true,
  registers: initialRegisters,
  memory: initialMemory,
  PC: 0,
};

const parseInstruction = (hexInstruction: string): RegisterUsage => {
  const binary = parseInt(hexInstruction, 16).toString(2).padStart(32, "0");
  const opcode = parseInt(binary.substring(0, 6), 2);
  const rs = parseInt(binary.substring(6, 11), 2);
  const rt = parseInt(binary.substring(11, 16), 2);

  let type: InstructionType = "R";
  let rd = 0;
  let funct = 0;
  let isLoad = false;
  let isStore = false;

  if (opcode === 0) {
    type = "R";
    rd = parseInt(binary.substring(16, 21), 2);
    funct = parseInt(binary.substring(26, 32), 2);
  } else if (opcode === 2 || opcode === 3) {
    type = "J";
    rd = opcode === 3 ? 31 : 0; // jal escribe en $ra
    funct = 0;
  } else {
    type = "I";
    // Identificar instrucciones de carga y almacenamiento
    if ([32, 33, 35, 36, 37, 48].includes(opcode)) { // lb, lh, lw, lbu, lhu, ll
      rd = rt; // rt es el destino para cargas
      isLoad = true;
    } else if ([40, 41, 43, 56].includes(opcode)) { // sb, sh, sw, sc
      rd = 0; // No hay registro destino para almacenes, rt es fuente
      isStore = true;
    } else if ([8, 9, 12, 13, 14, 15].includes(opcode)) { // addi, addiu, andi, ori, slti, sltiu
      rd = rt; // rt es el destino para instrucciones aritméticas inmediatas
    } else if (opcode === 15) { // lui
      rd = rt;
    } else {
      rd = 0;
    }
  }

  return { rs, rt, rd, opcode, funct, type, isLoad, isStore };
};

// Normalizar nombres de registros
const normalizeRegister = (reg: string): string => {
  reg = reg.toLowerCase().trim();
  if (reg.startsWith('$')) {
    return reg;
  }
  return `$${reg}`;
};

// Obtener valor de registro de manera segura
const getRegisterValue = (registers: Record<string, number>, regName: string): number => {
  const normalizedName = normalizeRegister(regName);
  return registers[normalizedName] || 0;
};

const executeMIPSInstruction = (
  hexInstruction: string,
  registers: Record<string, number>,
  memory: Record<number, number>,
  PC: number,
  stage: StageName,
  forwardings: ForwardingInfo[], // Añadido para manejar forwarding
  currentCycle: number
): number | undefined => {
  const mipsInstruction = translateInstructionToMIPS(hexInstruction);
  console.log(`Cycle ${currentCycle} - ${stage} - Executing instruction: ${hexInstruction} (${mipsInstruction})`);

  const [op, ...operands] = mipsInstruction.replace(/,/g, "").split(" ");
  let newPC: number | undefined;

  // Helper to convert register number to name
  const getRegName = (regNum: number) => `$${regMap[regNum.toString()] || `r${regNum}`}`;

  // Obtener valor de registro, considerando forwarding si está habilitado
  const getForwardedValue = (regNum: number, defaultValue: number): number => {
    const regName = getRegName(regNum);
    const forwarding = forwardings.find(
      (f) => f.register === regName && f.toStage === stage
    );
    if (forwarding) {
      console.log(`Forwarding ${regName} from ${forwarding.fromStage} to ${stage}`);
      return registers[regName]; // Valor ya actualizado en etapas previas
    }
    return defaultValue;
  };

  switch (stage) {
    case "EX": {
      switch (op) {
        case "add":
        case "addu": {
          const [rd, rs, rt] = operands.map((r: string) => normalizeRegister(r.replace('$', '')));
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rs]);
          const rtValue = getForwardedValue(parseInt(rt.replace('$', '')), registers[rt]);
          registers[rd] = rsValue + rtValue;
          console.log(`EX: ${op} ${rd}, ${rs}, ${rt} -> ${rd}=${registers[rd]}`);
          break;
        }
        case "addi":
        case "addiu": {
          const [rt, rs, immediate] = operands;
          const rtNorm = normalizeRegister(rt.replace('$', ''));
          const rsNorm = normalizeRegister(rs.replace('$', ''));
          const immValue = parseInt(immediate);
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rsNorm]);
          registers[rtNorm] = rsValue + immValue;
          console.log(`EX: ${op} ${rtNorm}, ${rsNorm}, ${immediate} -> ${rtNorm}=${registers[rtNorm]}`);
          break;
        }
        case "and": {
          const [rd, rs, rt] = operands.map((r: string) => normalizeRegister(r.replace('$', '')));
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rs]);
          const rtValue = getForwardedValue(parseInt(rt.replace('$', '')), registers[rt]);
          registers[rd] = rsValue & rtValue;
          console.log(`EX: and ${rd}, ${rs}, ${rt} -> ${rd}=${registers[rd]}`);
          break;
        }
        case "andi": {
          const [rt, rs, immediate] = operands;
          const rtNorm = normalizeRegister(rt.replace('$', ''));
          const rsNorm = normalizeRegister(rs.replace('$', ''));
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rsNorm]);
          registers[rtNorm] = rsValue & parseInt(immediate);
          console.log(`EX: andi ${rtNorm}, ${rsNorm}, ${immediate} -> ${rtNorm}=${registers[rtNorm]}`);
          break;
        }
        case "or": {
          const [rd, rs, rt] = operands.map((r: string) => normalizeRegister(r.replace('$', '')));
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rs]);
          const rtValue = getForwardedValue(parseInt(rt.replace('$', '')), registers[rt]);
          registers[rd] = rsValue | rtValue;
          console.log(`EX: or ${rd}, ${rs}, ${rt} -> ${rd}=${registers[rd]}`);
          break;
        }
        case "ori": {
          const [rt, rs, immediate] = operands;
          const rtNorm = normalizeRegister(rt.replace('$', ''));
          const rsNorm = normalizeRegister(rs.replace('$', ''));
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rsNorm]);
          registers[rtNorm] = rsValue | parseInt(immediate);
          console.log(`EX: ori ${rtNorm}, ${rsNorm}, ${immediate} -> ${rtNorm}=${registers[rtNorm]}`);
          break;
        }
        case "slt": {
          const [rd, rs, rt] = operands.map((r: string) => normalizeRegister(r.replace('$', '')));
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rs]);
          const rtValue = getForwardedValue(parseInt(rt.replace('$', '')), registers[rt]);
          registers[rd] = rsValue < rtValue ? 1 : 0;
          console.log(`EX: slt ${rd}, ${rs}, ${rt} -> ${rd}=${registers[rd]}`);
          break;
        }
        case "slti": {
          const [rt, rs, immediate] = operands;
          const rtNorm = normalizeRegister(rt.replace('$', ''));
          const rsNorm = normalizeRegister(rs.replace('$', ''));
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rsNorm]);
          registers[rtNorm] = rsValue < parseInt(immediate) ? 1 : 0;
          console.log(`EX: slti ${rtNorm}, ${rsNorm}, ${immediate} -> ${rtNorm}=${registers[rtNorm]}`);
          break;
        }
        case "sltiu": {
          const [rt, rs, immediate] = operands;
          const rtNorm = normalizeRegister(rt.replace('$', ''));
          const rsNorm = normalizeRegister(rs.replace('$', ''));
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rsNorm]);
          registers[rtNorm] = (rsValue >>> 0) < (parseInt(immediate) >>> 0) ? 1 : 0;
          console.log(`EX: sltiu ${rtNorm}, ${rsNorm}, ${immediate} -> ${rtNorm}=${registers[rtNorm]}`);
          break;
        }
        case "sltu": {
          const [rd, rs, rt] = operands.map((r: string) => normalizeRegister(r.replace('$', '')));
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rs]);
          const rtValue = getForwardedValue(parseInt(rt.replace('$', '')), registers[rt]);
          registers[rd] = (rsValue >>> 0) < (rtValue >>> 0) ? 1 : 0;
          console.log(`EX: sltu ${rd}, ${rs}, ${rt} -> ${rd}=${registers[rd]}`);
          break;
        }
        case "sll": {
          const [rd, rt, shamt] = operands;
          const rtNorm = normalizeRegister(rt.replace('$', ''));
          const rdNorm = normalizeRegister(rd.replace('$', ''));
          const rtValue = getForwardedValue(parseInt(rt.replace('$', '')), registers[rtNorm]);
          registers[rdNorm] = rtValue << parseInt(shamt);
          console.log(`EX: sll ${rdNorm}, ${rtNorm}, ${shamt} -> ${rdNorm}=${registers[rdNorm]}`);
          break;
        }
        case "srl": {
          const [rd, rt, shamt] = operands;
          const rtNorm = normalizeRegister(rt.replace('$', ''));
          const rdNorm = normalizeRegister(rd.replace('$', ''));
          const rtValue = getForwardedValue(parseInt(rt.replace('$', '')), registers[rtNorm]);
          registers[rdNorm] = rtValue >>> parseInt(shamt);
          console.log(`EX: srl ${rdNorm}, ${rtNorm}, ${shamt} -> ${rdNorm}=${registers[rdNorm]}`);
          break;
        }
        case "sub":
        case "subu": {
          const [rd, rs, rt] = operands.map((r: string) => normalizeRegister(r.replace('$', '')));
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rs]);
          const rtValue = getForwardedValue(parseInt(rt.replace('$', '')), registers[rt]);
          registers[rd] = rsValue - rtValue;
          console.log(`EX: ${op} ${rd}, ${rs}, ${rt} -> ${rd}=${registers[rd]}`);
          break;
        }
        case "nor": {
          const [rd, rs, rt] = operands.map((r: string) => normalizeRegister(r.replace('$', '')));
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rs]);
          const rtValue = getForwardedValue(parseInt(rt.replace('$', '')), registers[rt]);
          registers[rd] = ~(rsValue | rtValue);
          console.log(`EX: nor ${rd}, ${rs}, ${rt} -> ${rd}=${registers[rd]}`);
          break;
        }
        case "beq": {
          const [rs, rt, offset] = operands;
          const rsNorm = normalizeRegister(rs.replace('$', ''));
          const rtNorm = normalizeRegister(rt.replace('$', ''));
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rsNorm]);
          const rtValue = getForwardedValue(parseInt(rt.replace('$', '')), registers[rtNorm]);
          if (rsValue === rtValue) {
            newPC = PC + 1 + parseInt(offset);
            console.log(`EX: beq ${rsNorm}, ${rtNorm}, ${offset} -> Branch taken, new PC=${newPC}`);
          } else {
            console.log(`EX: beq ${rsNorm}, ${rtNorm}, ${offset} -> Branch not taken`);
          }
          break;
        }
        case "bne": {
          const [rs, rt, offset] = operands;
          const rsNorm = normalizeRegister(rs.replace('$', ''));
          const rtNorm = normalizeRegister(rt.replace('$', ''));
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rsNorm]);
          const rtValue = getForwardedValue(parseInt(rt.replace('$', '')), registers[rtNorm]);
          if (rsValue !== rtValue) {
            newPC = PC + 1 + parseInt(offset);
            console.log(`EX: bne ${rsNorm}, ${rtNorm}, ${offset} -> Branch taken, new PC=${newPC}`);
          } else {
            console.log(`EX: bne ${rsNorm}, ${rtNorm}, ${offset} -> Branch not taken`);
          }
          break;
        }
        case "j": {
          const [target] = operands;
          newPC = parseInt(target, 16) >> 2; // Ajustar para direcciones de palabras
          console.log(`EX: j ${target} -> new PC=${newPC}`);
          break;
        }
        case "jal": {
          const [target] = operands;
          registers["$ra"] = PC + 2;
          newPC = parseInt(target, 16) >> 2; // Ajustar para direcciones de palabras
          console.log(`EX: jal ${target} -> $ra=${registers["$ra"]}, new PC=${newPC}`);
          break;
        }
        case "jr": {
          const [rs] = operands;
          const rsNorm = normalizeRegister(rs.replace('$', ''));
          const rsValue = getForwardedValue(parseInt(rs.replace('$', '')), registers[rsNorm]);
          newPC = rsValue >> 2; // Ajustar para direcciones de palabras
          console.log(`EX: jr ${rsNorm} -> new PC=${newPC}`);
          break;
        }
        case "lui": {
          const [rt, immediate] = operands;
          const rtNorm = normalizeRegister(rt.replace('$', ''));
          registers[rtNorm] = parseInt(immediate) << 16;
          console.log(`EX: lui ${rtNorm}, ${immediate} -> ${rtNorm}=${registers[rtNorm]}`);
          break;
        }
      }
      break;
    }
    case "MEM": {
      switch (op) {
        case "lw":
        case "sw": {
          const [rt, offsetAndBase] = operands;
          const rtNorm = normalizeRegister(rt.replace('$', ''));
          const offsetMatch = /^(-?\d+)\(\$(\w+)\)$/.exec(offsetAndBase);
          if (!offsetMatch) {
            console.error(`MEM: Invalid offset/base format: ${offsetAndBase}`);
            break;
          }
          const [, offsetStr, baseReg] = offsetMatch;
          const offset = parseInt(offsetStr);
          const baseRegNorm = normalizeRegister(baseReg);
          const baseValue = getForwardedValue(parseInt(baseReg.replace('$', '')), registers[baseRegNorm]);
          const address = (baseValue + offset) >>> 0;

          // Solo validar que la dirección esté dentro de los límites de la memoria (0-31)
          if (address < 0 || address >= 32) {
            console.error(`MEM: Invalid memory address for ${op}: ${address}`);
            break;
          }

          if (op === "lw") {
            registers[rtNorm] = memory[address] || 0;
            console.log(`MEM: lw ${rtNorm}, ${offset}(${baseRegNorm}) -> ${rtNorm}=${registers[rtNorm]} from address ${address}`);
          } else { // sw
            const valueToStore = getForwardedValue(parseInt(rt.replace('$', '')), registers[rtNorm]);
            memory[address] = valueToStore;
            console.log(`MEM: sw ${rtNorm}, ${offset}(${baseRegNorm}) -> Memory[${address}]=${valueToStore}`);
          }
          break;
        }
        case "lbu":
        case "lhu":
        case "ll":
        case "sb":
        case "sh":
        case "sc": {
          const [rt, offsetAndBase] = operands;
          const rtNorm = normalizeRegister(rt.replace('$', ''));
          const offsetMatch = /^(-?\d+)\(\$(\w+)\)$/.exec(offsetAndBase);
          if (!offsetMatch) {
            console.error(`MEM: Invalid offset/base format: ${offsetAndBase}`);
            break;
          }
          const [, offsetStr, baseReg] = offsetMatch;
          const offset = parseInt(offsetStr);
          const baseRegNorm = normalizeRegister(baseReg);
          const baseValue = getForwardedValue(parseInt(baseReg.replace('$', '')), registers[baseRegNorm]);
          const address = (baseValue + offset) >>> 0;

          // Validar que la dirección esté dentro de los límites de la memoria (0-31)
          if (address < 0 || address > 31) {
            console.error(`MEM: Invalid memory address for ${op}: ${address}`);
            break;
          }

          if (op === "lbu") {
            registers[rtNorm] = (memory[address] || 0) & 0xFF;
            console.log(`MEM: lbu ${rtNorm}, ${offset}(${baseRegNorm}) -> ${rtNorm}=${registers[rtNorm]} from address ${address}`);
          } else if (op === "lhu") {
            registers[rtNorm] = (memory[address] || 0) & 0xFFFF;
            console.log(`MEM: lhu ${rtNorm}, ${offset}(${baseRegNorm}) -> ${rtNorm}=${registers[rtNorm]} from address ${address}`);
          } else if (op === "ll") {
            registers[rtNorm] = memory[address] || 0;
            console.log(`MEM: ll ${rtNorm}, ${offset}(${baseRegNorm}) -> ${rtNorm}=${registers[rtNorm]} from address ${address}`);
          } else if (op === "sb") {
            const valueToStore = getForwardedValue(parseInt(rt.replace('$', '')), registers[rtNorm]);
            memory[address] = valueToStore & 0xFF;
            console.log(`MEM: sb ${rtNorm}, ${offset}(${baseRegNorm}) -> Memory[${address}]=${memory[address]}`);
          } else if (op === "sh") {
            const valueToStore = getForwardedValue(parseInt(rt.replace('$', '')), registers[rtNorm]);
            memory[address] = valueToStore & 0xFFFF;
            console.log(`MEM: sh ${rtNorm}, ${offset}(${baseRegNorm}) -> Memory[${address}]=${memory[address]}`);
          } else if (op === "sc") {
            const valueToStore = getForwardedValue(parseInt(rt.replace('$', '')), registers[rtNorm]);
            memory[address] = valueToStore;
            registers[rtNorm] = 1;
            console.log(`MEM: sc ${rtNorm}, ${offset}(${baseRegNorm}) -> Memory[${address}]=${valueToStore}, ${rtNorm}=${registers[rtNorm]}`);
          }
          break;
        }
      }
      break;
    }
    case "WB": {
      console.log(`WB: Registers after instruction:`, { ...registers });
      console.log(`WB: Memory after instruction:`, { ...memory });
      break;
    }
  }

  // Asegurar que $zero siempre sea 0
  registers["$zero"] = 0;

  return newPC;
};

const detectHazards = (
  instructions: string[],
  registerUsage: Record<number, RegisterUsage>,
  forwardingEnabled: boolean,
  stallsEnabled: boolean
): [
  Record<number, HazardInfo>,
  Record<number, ForwardingInfo[]>,
  Record<number, number>
] => {
  const hazards: Record<number, HazardInfo> = {};
  const forwardings: Record<number, ForwardingInfo[]> = {};
  const stalls: Record<number, number> = {};

  // Initialize all instructions with no hazard
  instructions.forEach((_, index) => {
    hazards[index] = {
      type: "NONE",
      description: "No hazard",
      canForward: false,
      stallCycles: 0,
    };
    forwardings[index] = [];
    stalls[index] = 0;
  });

  if (!stallsEnabled) {
    return [hazards, forwardings, stalls];
  }

  for (let i = 1; i < instructions.length; i++) {
    const currentInst = registerUsage[i];

    if (currentInst.type === "J") continue;

    for (let j = i - 1; j >= 0 && i - j <= 3; j--) { // Revisar hasta 3 instrucciones previas
      const prevInst = registerUsage[j];

      if (prevInst.rd === 0 && !prevInst.isLoad) continue;

      let hasRawHazard = false;
      let hazardRegister = "";

      // Verificar RAW hazards
      if (currentInst.rs !== 0 && currentInst.rs === prevInst.rd) {
        hasRawHazard = true;
        hazardRegister = `rs($${regMap[currentInst.rs.toString()]})`;
      } else if (
        currentInst.rt !== 0 &&
        currentInst.rt === prevInst.rd &&
        (currentInst.isStore || (!currentInst.isLoad && currentInst.type !== "I"))
      ) {
        hasRawHazard = true;
        hazardRegister = `rt($${regMap[currentInst.rt.toString()]})`;
      }

      if (hasRawHazard) {
        const distance = i - j;
        if (prevInst.isLoad) {
          // Load-use hazard
          if (distance === 1) {
            hazards[i] = {
              type: "RAW",
              description: `Load-use hazard: ${hazardRegister} depends on lw in instruction ${j}`,
              canForward: forwardingEnabled,
              stallCycles: forwardingEnabled ? 0 : 1,
            };
            stalls[i] = forwardingEnabled ? 0 : 1;
            if (forwardingEnabled) {
              forwardings[i] = [
                ...forwardings[i],
                {
                  from: j,
                  to: i,
                  fromStage: "MEM",
                  toStage: "EX",
                  register: `$${regMap[prevInst.rd.toString()]}`,
                },
              ];
            }
          }
        } else {
          // Regular RAW hazard
          if (forwardingEnabled) {
            hazards[i] = {
              type: "RAW",
              description: `RAW hazard: ${hazardRegister} depends on instruction ${j} (forwarded)`,
              canForward: true,
              stallCycles: 0,
            };
            forwardings[i] = [
              ...forwardings[i],
              {
                from: j,
                to: i,
                fromStage: distance === 1 ? "EX" : "MEM",
                toStage: "EX",
                register: `$${regMap[prevInst.rd.toString()]}`,
              },
            ];
          } else {
            hazards[i] = {
              type: "RAW",
              description: `RAW hazard: ${hazardRegister} depends on instruction ${j} (no forwarding)`,
              canForward: false,
              stallCycles: distance === 1 ? 2 : 1,
            };
            stalls[i] = distance === 1 ? 2 : 1;
          }
        }
      }

      // Verificar WAW hazards
      if (
        currentInst.rd !== 0 &&
        currentInst.rd === prevInst.rd &&
        !hasRawHazard
      ) {
        hazards[i] = {
          type: "WAW",
          description: `WAW hazard: Both instructions write to $${regMap[currentInst.rd.toString()]}`,
          canForward: true,
          stallCycles: 0,
        };
      }
    }
  }

  return [hazards, forwardings, stalls];
};

const calculatePrecedingStalls = (
  stalls: Record<number, number>,
  index: number
): number => {
  let totalStalls = 0;
  for (let i = 0; i < index; i++) {
    totalStalls += stalls[i] || 0;
  }
  return totalStalls;
};

const calculateNextState = (currentState: SimulationState): SimulationState => {
  if (!currentState.isRunning || currentState.isFinished) {
    return currentState;
  }

  const nextCycle = currentState.currentCycle + 1;
  const newInstructionStages: Record<number, number | null> = {};
  let activeInstructions = 0;

  let newStallCycles = currentState.currentStallCycles;

  let newRegisters = { ...currentState.registers };
  let newMemory = { ...currentState.memory };
  let newPC = currentState.PC;

  if (newStallCycles > 0) {
    newStallCycles--;
    return {
      ...currentState,
      currentCycle: nextCycle,
      instructionStages: currentState.instructionStages,
      currentStallCycles: newStallCycles,
      registers: newRegisters,
      memory: newMemory,
      PC: newPC,
    };
  }

  let totalStallCycles = 0;
  Object.values(currentState.stalls).forEach((stalls) => {
    totalStallCycles += stalls;
  });

  currentState.instructions.forEach((inst, index) => {
    const precedingStalls = calculatePrecedingStalls(currentState.stalls, index);
    const stageIndex = nextCycle - index - 1 - precedingStalls;

    if (stageIndex >= 0 && stageIndex < currentState.stageCount) {
      newInstructionStages[index] = stageIndex;
      activeInstructions++;

      if (
        stageIndex === 1 &&
        currentState.stalls[index] > 0 &&
        newStallCycles === 0
      ) {
        newStallCycles = currentState.stalls[index];
      }

      // Ejecutar instrucción en la etapa adecuada
      if (stageIndex === 2) { // EX stage
        const updatedPC = executeMIPSInstruction(
          inst,
          newRegisters,
          newMemory,
          newPC,
          "EX",
          currentState.forwardings[index] || [],
          nextCycle
        );
        if (updatedPC !== undefined) {
          newPC = updatedPC;
        }
      } else if (stageIndex === 3) { // MEM stage
        executeMIPSInstruction(
          inst,
          newRegisters,
          newMemory,
          newPC,
          "MEM",
          currentState.forwardings[index] || [],
          nextCycle
        );
      } else if (stageIndex === 4) { // WB stage
        executeMIPSInstruction(
          inst,
          newRegisters,
          newMemory,
          newPC,
          "WB",
          currentState.forwardings[index] || [],
          nextCycle
        );
      }
    } else {
      newInstructionStages[index] = null;
    }
  });

  const completionCycle =
    currentState.instructions.length > 0
      ? currentState.instructions.length +
        currentState.stageCount - 1 +
        totalStallCycles
      : 0;

  const isFinished = nextCycle > completionCycle;
  const isRunning = !isFinished;

  if (!isFinished && newPC !== currentState.PC) {
    // Actualizar instrucciones y etapas basadas en el nuevo PC
    const newInstructions = currentState.instructions.slice(newPC);
    const newInstructionStages: Record<number, number | null> = {};
    newInstructions.forEach((_, index) => {
      const stageIndex = nextCycle - index - 1 - calculatePrecedingStalls(currentState.stalls, index + newPC);
      newInstructionStages[index + newPC] = stageIndex >= 0 && stageIndex < currentState.stageCount ? stageIndex : null;
    });
    return {
      ...currentState,
      instructions: newInstructions,
      currentCycle: nextCycle,
      instructionStages: newInstructionStages,
      isRunning,
      isFinished,
      currentStallCycles: newStallCycles,
      registers: newRegisters,
      memory: newMemory,
      PC: newPC,
    };
  }

  return {
    ...currentState,
    currentCycle: isFinished ? completionCycle : nextCycle,
    instructionStages: newInstructionStages,
    isRunning: isRunning,
    isFinished: isFinished,
    currentStallCycles: newStallCycles,
    registers: newRegisters,
    memory: newMemory,
    PC: newPC,
  };
};

export function SimulationProvider({ children }: PropsWithChildren) {
  const [simulationState, setSimulationState] =
    useState<SimulationState>(initialState);
  const intervalRef = useRef<NodeJS.Timeout | null>(null);

  const clearTimer = () => {
    if (intervalRef.current) {
      clearInterval(intervalRef.current);
      intervalRef.current = null;
    }
  };

  const runClock = useCallback(() => {
    clearTimer();
    if (!simulationState.isRunning || simulationState.isFinished) return;

    intervalRef.current = setInterval(() => {
      setSimulationState((prevState) => {
        const nextState = calculateNextState(prevState);
        if (nextState.isFinished && !prevState.isFinished) {
          clearTimer();
        }
        return nextState;
      });
    }, 500);
  }, [simulationState.isRunning, simulationState.isFinished]);

  const resetSimulation = useCallback(() => {
    clearTimer();
    setSimulationState((prevState) => ({
      ...initialState,
      forwardingEnabled: prevState.forwardingEnabled,
      stallsEnabled: prevState.stallsEnabled,
    }));
  }, []);

  const startSimulation = useCallback(
    (submittedInstructions: string[]) => {
      clearTimer();
      if (submittedInstructions.length === 0) {
        resetSimulation();
        return;
      }

      const registerUsage: Record<number, RegisterUsage> = {};
      submittedInstructions.forEach((inst, index) => {
        registerUsage[index] = parseInstruction(inst);
      });

      const [hazards, forwardings, stalls] = detectHazards(
        submittedInstructions,
        registerUsage,
        simulationState.forwardingEnabled,
        simulationState.stallsEnabled
      );

      let totalStallCycles = 0;
      Object.values(stalls).forEach((stall) => {
        totalStallCycles += stall;
      });

      const calculatedMaxCycles =
        submittedInstructions.length +
        DEFAULT_STAGE_COUNT - 1 +
        totalStallCycles;
      const initialStages: Record<number, number | null> = {};

      submittedInstructions.forEach((_, index) => {
        const stageIndex = 1 - index - 1;
        if (stageIndex >= 0 && stageIndex < DEFAULT_STAGE_COUNT) {
          initialStages[index] = stageIndex;
        } else {
          initialStages[index] = null;
        }
      });

      setSimulationState({
        instructions: submittedInstructions,
        currentCycle: 1,
        maxCycles: calculatedMaxCycles,
        isRunning: true,
        stageCount: DEFAULT_STAGE_COUNT,
        instructionStages: initialStages,
        isFinished: false,
        registerUsage,
        hazards,
        forwardings,
        stalls,
        currentStallCycles: 0,
        forwardingEnabled: simulationState.forwardingEnabled,
        stallsEnabled: simulationState.stallsEnabled,
        registers: { ...initialRegisters },
        memory: { ...initialMemory },
        PC: 0,
      });
    },
    [
      resetSimulation,
      simulationState.forwardingEnabled,
      simulationState.stallsEnabled,
    ]
  );

  const pauseSimulation = () => {
    setSimulationState((prevState) => {
      if (prevState.isRunning) {
        clearTimer();
        return { ...prevState, isRunning: false };
      }
      return prevState;
    });
  };

  const resumeSimulation = () => {
    setSimulationState((prevState) => {
      if (
        !prevState.isRunning &&
        prevState.currentCycle > 0 &&
        !prevState.isFinished
      ) {
        return { ...prevState, isRunning: true };
      }
      return prevState;
    });
  };

  const setForwardingEnabled = (enabled: boolean) => {
    setSimulationState((prevState) => {
      return { ...prevState, forwardingEnabled: enabled };
    });
  };

  const setStallsEnabled = (enabled: boolean) => {
    setSimulationState((prevState) => {
      return { ...prevState, stallsEnabled: enabled };
    });
  };

  useEffect(() => {
    if (simulationState.isRunning && !simulationState.isFinished) {
      runClock();
    } else {
      clearTimer();
    }
    return clearTimer;
  }, [simulationState.isRunning, simulationState.isFinished, runClock]);

  const stateValue: SimulationState = simulationState;

  const actionsValue: SimulationActions = useMemo(
    () => ({
      startSimulation,
      resetSimulation,
      pauseSimulation,
      resumeSimulation,
      setForwardingEnabled,
      setStallsEnabled,
    }),
    [startSimulation, resetSimulation]
  );

  return (
    <SimulationStateContext.Provider value={stateValue}>
      <SimulationActionsContext.Provider value={actionsValue}>
        {children}
      </SimulationActionsContext.Provider>
    </SimulationStateContext.Provider>
  );
}

export function useSimulationState() {
  const context = useContext(SimulationStateContext);
  if (context === undefined) {
    throw new Error("useSimulationState must be used within a SimulationProvider");
  }
  return context;
}

export function useSimulationActions() {
  const context = useContext(SimulationActionsContext);
  if (context === undefined) {
    throw new Error("useSimulationActions must be used within a SimulationProvider");
  }
  return context;
}