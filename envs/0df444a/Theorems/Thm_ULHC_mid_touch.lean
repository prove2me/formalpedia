-- Prove2me | Theorems.Thm_ULHC_mid_touch
-- name    : ULHC.mid_touch
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:00:12.943979+00:00
-- url     : https://prove2.me/theorems/1734f356-f079-4bca-8f08-1e8c333b9c93
-- title:
--   ULHC: mid touch
-- statement:
--   The ULHC construction uses the mid touch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearGeo.lean#L60-L89
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearGeo.lean#L60-L89

import Definitions.Def_ULHC_Touch
import Definitions.Def_ULHC_Stacked
import Definitions.Def_ULHC_NearGeo
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hpat : StripPat F c s (k + 2))
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
include hF hpat hcell

theorem ULHC.mid_touch {p : Pt} (hm : IsMid c s k p) {x : Edge} (hx : x ∈ F) (hxp : x.p = p ∨ x.q = p) :
    ∃ j < k + 2, x ∈ cellE (cellJ c s j) := by sorry
