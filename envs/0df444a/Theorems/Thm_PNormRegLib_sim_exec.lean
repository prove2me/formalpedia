-- Prove2me | Theorems.Thm_PNormRegLib_sim_exec
-- name    : PNormRegLib.sim_exec
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T08:37:06.817893+00:00
-- url     : https://prove2.me/theorems/d8a0b02b-72ab-4d66-86a7-0e5f17793685
-- title:
--   One step of a relocated real-RAM program
-- statement:
--   Let $p$ be relocation parameters and $F$ a frame forming a valid pair (definitions `PNormRegLib_Reloc` and `PNormRegLib_Simulation`), and write $\omega_k(i)=\omega(i+k)$ for the coin tape $\omega$ shifted by the cursor offset $k$ of $F$. Let $\iota$ be an instruction within the index bounds of $F$ other than `accept`, `reject` and `halt`. Suppose the host state $r$ represents the virtual state $v$, the program counter of $r$ is $c_0+2\cdot(\text{program counter of }v)$, and $v$ is $X$-bounded (definition `PNormRegLib_AddressBound`) with $X\le R$. Let
--
--   $$r'=\mathrm{exec}_\omega(\mathrm{main}\,\iota,\ \mathrm{exec}_\omega(\mathrm{prep}\,\iota,\ r)),\qquad v'=\mathrm{exec}_{\omega_k}(\iota,v).$$
--
--   Then $r'$ represents $v'$, the program counter of $r'$ is $c_0+2\cdot(\text{program counter of }v')$, and neither halted flag changes.
--
--   This is the inductive step of the simulation theorem `PNormRegLib.reloc_sim`: one virtual step is two host steps.
-- source:
--   Original library result for the PNormReg machine (definition PNormReg_Machine: Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission), written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' at the captain's invitation (mission discussion, 2026-11-14). No external source is claimed; relocating a program by shifting its jump targets and memory accesses is the standard technique for composing machine programs.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation

namespace PNormRegLib

open PNormReg

/-- **One virtual step is two real steps.** Let `ins` be an instruction other than `accept`,
`reject` and `halt`, within the index bounds of `F`. If the real state `r` represents the virtual
state `v` (`Agree`), with the real program counter at the relocated position, and every pointer of
`v` lies within the window (`PBounded X v`, `X ≤ R`), then executing the relocated pair of `ins` on
`r` represents executing `ins` on `v` (on the tape shifted by `k`): `Agree` is preserved, the real
program counter is again at the relocated position, and neither halted flag changes. -/
theorem sim_exec (p : RelocParams) (F : Frame) (ω : ℕ → Bool) (ins : Instr) (X : ℤ) (r v : State)
    (hV : Valid p F) (hok : InstrOK F.nR F.nQ ins) (hA : Agree p F r v)
    (hpc : r.core.pc = p.cOff + 2 * v.core.pc) (hBd : PBounded X v) (hXR : X ≤ F.R)
    (hlive : ins ≠ .core .accept ∧ ins ≠ .core .reject ∧ ins ≠ .halt) :
    Agree p F (exec ω (p.pair ins).2 (exec ω (p.pair ins).1 r))
        (exec (fun i => ω (i + F.k)) ins v) ∧
      (exec ω (p.pair ins).2 (exec ω (p.pair ins).1 r)).core.pc =
        p.cOff + 2 * (exec (fun i => ω (i + F.k)) ins v).core.pc ∧
      (exec ω (p.pair ins).2 (exec ω (p.pair ins).1 r)).halted = r.halted ∧
      (exec (fun i => ω (i + F.k)) ins v).halted = v.halted := by sorry

end PNormRegLib
