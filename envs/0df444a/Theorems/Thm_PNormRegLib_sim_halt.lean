-- Prove2me | Theorems.Thm_PNormRegLib_sim_halt
-- name    : PNormRegLib.sim_halt
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T08:37:06.965582+00:00
-- url     : https://prove2.me/theorems/e9b132fa-503c-4133-ae5f-bf60fc9534d0
-- title:
--   The relocated halt jumps to the exit label
-- statement:
--   Let $p$ be relocation parameters and $F$ a frame (definitions `PNormRegLib_Reloc` and `PNormRegLib_Simulation`), and write $\omega_k(i)=\omega(i+k)$ for the coin tape $\omega$ shifted by the cursor offset $k$ of $F$. Suppose the host state $r$ represents the virtual state $v$, and let
--
--   $$r'=\mathrm{exec}_\omega(\mathrm{main}\,\mathtt{halt},\ \mathrm{exec}_\omega(\mathrm{prep}\,\mathtt{halt},\ r)),\qquad v'=\mathrm{exec}_{\omega_k}(\mathtt{halt},v).$$
--
--   Then $r'$ represents $v'$, the program counter of $r'$ is the exit label $e$, the halted flag of $r'$ is that of $r$, and $v'$ is halted.
--
--   This is the last step of the simulation theorem `PNormRegLib.reloc_sim`: where the copied program stops, the host continues at the exit label.
-- source:
--   Original library result for the PNormReg machine (definition PNormReg_Machine: Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission), written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' at the captain's invitation (mission discussion, 2026-11-14). No external source is claimed; relocating a program by shifting its jump targets and memory accesses is the standard technique for composing machine programs.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation

namespace PNormRegLib

open PNormReg

/-- **The relocated `halt`.** If `r` represents `v`, then executing the relocated pair of `halt` on
`r` reaches the exit label without halting, while `halt` halts `v`; `Agree` is preserved. -/
theorem sim_halt (p : RelocParams) (F : Frame) (ω : ℕ → Bool) (r v : State)
    (hA : Agree p F r v) :
    Agree p F (exec ω (p.pair .halt).2 (exec ω (p.pair .halt).1 r))
        (exec (fun i => ω (i + F.k)) .halt v) ∧
      (exec ω (p.pair .halt).2 (exec ω (p.pair .halt).1 r)).core.pc = p.exit ∧
      (exec ω (p.pair .halt).2 (exec ω (p.pair .halt).1 r)).halted = r.halted ∧
      (exec (fun i => ω (i + F.k)) .halt v).halted = true := by sorry

end PNormRegLib
