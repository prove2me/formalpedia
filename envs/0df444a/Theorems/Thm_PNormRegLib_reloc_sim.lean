-- Prove2me | Theorems.Thm_PNormRegLib_reloc_sim
-- name    : PNormRegLib.reloc_sim
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T08:37:10.154006+00:00
-- url     : https://prove2.me/theorems/4ef3c407-25ad-4ebd-9fdb-f10e5a71bd0c
-- title:
--   Simulation theorem for relocated real-RAM programs
-- statement:
--   Let $p$ be relocation parameters and $F$ a frame forming a valid pair (definitions `PNormRegLib_Reloc` and `PNormRegLib_Simulation`), and write $\omega_k(i)=\omega(i+k)$ for the coin tape $\omega$ shifted by the cursor offset $k$ of $F$. Let $P$ and $Q$ be programs such that:
--
--   1. $Q$ embeds $\mathrm{reloc}_p(P)$ at offset $c_0$, and $P$ uses indices below $(n_R,n_Q)$;
--   2. $X\ge1$ is a literal bound of $P$ (definition `PNormRegLib_AddressBound`);
--   3. the host state $r$ and the virtual state $v$ are in simulation, and $v$ is $Y$-bounded with $X\le Y$ and $Y\cdot2^t\le R$.
--
--   If $P$, run from $v$ on $\omega_k$, is halted after $t$ steps, then there is $t'$ such that $Q$, run from $r$ on $\omega$ for $t'$ steps, reaches a running state at the exit label $e$ that represents the state of $P$ after $t$ steps:
--
--   $$\exists\,t'\quad \mathrm{run}_Q(r,\omega,t')\ \text{represents}\ \mathrm{run}_P(v,\omega_k,t),\qquad \mathrm{pc}=e,\qquad \text{not halted}.$$
--
--   In particular the host work is $c$ plus twice the virtual work, the host memory on the window $b+[-R,R]$ is the final virtual memory, and the memory outside the window is unchanged. This is the composition theorem that lets a program known only to exist run as a subroutine of a larger program.
-- source:
--   Original library result for the PNormReg machine (definition PNormReg_Machine: Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission), written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' at the captain's invitation (mission discussion, 2026-11-14). No external source is claimed; relocating a program by shifting its jump targets and memory accesses is the standard technique for composing machine programs.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation

namespace PNormRegLib

open PNormReg

/-- **Simulation theorem.** Let the host program `Q` contain the relocated copy of `P` at position
`p.cOff`, and let the real state `r` represent the running virtual state `v` (`Sim`). Suppose `v` is
`PBounded Y`, where `Y` is at least a literal bound `X ≥ 1` of `P`, and the window radius is at least
`Y · 2^t`. If `P` halts from `v` within `t` steps (on the tape shifted by `k`), then `Q` reaches from
`r` a running state at the exit label that represents the halted virtual state. -/
theorem reloc_sim (p : RelocParams) (F : Frame) (P Q : Program) (ω : ℕ → Bool) (X : ℤ)
    (hE : Embeds Q (reloc p P) p.cOff) (hV : Valid p F) (hU : UsesBelow P F.nR F.nQ)
    (hlit : LitBound P X) (hX : 1 ≤ X) (t : ℕ) (Y : ℤ) (r v : State) (hS : Sim p F r v)
    (hB : PBounded Y v) (hXY : X ≤ Y) (hR : Y * 2 ^ t ≤ F.R)
    (hh : (run P v (fun i => ω (i + F.k)) t).halted = true) :
    ∃ t', Agree p F (run Q r ω t') (run P v (fun i => ω (i + F.k)) t) ∧
      (run Q r ω t').core.pc = p.exit ∧ (run Q r ω t').halted = false := by sorry

end PNormRegLib
