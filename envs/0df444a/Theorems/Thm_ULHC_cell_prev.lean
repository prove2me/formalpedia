-- Prove2me | Theorems.Thm_ULHC_cell_prev
-- name    : ULHC.cell_prev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:20:58.700544+00:00
-- url     : https://prove2.me/theorems/c02e7ee9-26f0-4321-8ab4-5ac5b00e4cfe
-- title:
--   ULHC: cell prev
-- statement:
--   The ULHC construction uses the cell prev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L322-L325
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L322-L325

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i i0 : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)

theorem ULHC.cell_prev {z : Pt} {tf : Side} {i : ℕ} (hi : 1 ≤ i) :
    cellJ z tf (i - 1) = nb (cellJ z tf i) tf.opp := by sorry
