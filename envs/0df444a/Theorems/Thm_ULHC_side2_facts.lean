-- Prove2me | Theorems.Thm_ULHC_side2_facts
-- name    : ULHC.side2_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:02:09.356146+00:00
-- url     : https://prove2.me/theorems/b2ed8014-42eb-44b3-88e0-7f54eb95403c
-- title:
--   ULHC: side2 facts
-- statement:
--   The ULHC construction uses the side2 facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L422-L434
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L422-L434

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
include hF hT hk hcell hpat hsep

theorem ULHC.side2_facts {j : ℕ} (hj : j ≤ k) :
    (lat1 (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1) ∧
      (back (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1) ∧
      (front (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 0) := by sorry
