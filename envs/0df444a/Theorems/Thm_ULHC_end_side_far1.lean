-- Prove2me | Theorems.Thm_ULHC_end_side_far1
-- name    : ULHC.end_side_far1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:25:49.655262+00:00
-- url     : https://prove2.me/theorems/68838139-27f5-4b84-b49e-ec2a20807815
-- title:
--   ULHC: end side far1
-- statement:
--   The ULHC construction uses the end side far1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L231-L249
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L231-L249

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
include hF hT hk hcell hpat

theorem ULHC.end_side_far1 (hb : outer1 (cellJ c s k) s ∈ F) (hf : outer1 (cellJ c s (k + 1)) s ∈ F) :
    lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F := by sorry
