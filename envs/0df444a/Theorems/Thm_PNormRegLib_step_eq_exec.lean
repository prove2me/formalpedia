-- Prove2me | Theorems.Thm_PNormRegLib_step_eq_exec
-- name    : PNormRegLib.step_eq_exec
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T08:11:02.954936+00:00
-- url     : https://prove2.me/theorems/21584878-0259-437a-bf74-fa24e0fef163
-- title:
--   One step of the real RAM executes the fetched instruction
-- statement:
--   Let $P$ be a program of the real RAM `PNormReg_Machine`, $\omega$ a coin tape and $s$ a state that is not halted, and suppose the instruction of $P$ at the program counter of $s$ is $\iota$. Then
--
--   $$\mathrm{step}_{P,\omega}(s)=\mathrm{exec}_\omega(\iota,s),$$
--
--   where $\mathrm{exec}$ is the single-instruction semantics of the definition `PNormRegLib_Exec`.
--
--   This is the bridge between the machine's step function and per-instruction reasoning: once the fetched instruction is known, a step can be computed without the program.
-- source:
--   Restatement of PNormReg.step (definition PNormReg_Machine) and SmaleNinth.RAMStep (definition SmaleNinth_RealRAM), split by instruction; original library definition, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions'.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec

namespace PNormRegLib

open PNormReg

/-- In a running state whose program counter holds `ins`, one step of the machine is `exec ins`. -/
theorem step_eq_exec (P : Program) (ω : ℕ → Bool) (s : State) (ins : Instr)
    (hh : s.halted = false) (h : P[s.core.pc]? = some ins) : step P ω s = exec ω ins s := by sorry

end PNormRegLib
