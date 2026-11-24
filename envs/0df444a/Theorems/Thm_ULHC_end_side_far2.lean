-- Prove2me | Theorems.Thm_ULHC_end_side_far2
-- name    : ULHC.end_side_far2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:25:46.316583+00:00
-- url     : https://prove2.me/theorems/d4082040-2e41-4eca-85e3-3ae1ebe7f33a
-- title:
--   ULHC: end side far2
-- statement:
--   The ULHC construction uses the end side far2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L258-L277
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L258-L277

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

theorem ULHC.end_side_far2 (hb : outer2 (cellJ c s k) s ∈ F) (hf : outer2 (cellJ c s (k + 1)) s ∈ F) :
    lat2 (nb (cellJ c s (k + 1)) (latB s)) s ∉ F := by sorry
