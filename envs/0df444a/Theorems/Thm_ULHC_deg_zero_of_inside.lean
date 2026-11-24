-- Prove2me | Theorems.Thm_ULHC_deg_zero_of_inside
-- name    : ULHC.deg_zero_of_inside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:47:37.445544+00:00
-- url     : https://prove2.me/theorems/daaa3df2-74de-4a93-884b-53823dbba3e9
-- title:
--   ULHC: deg zero of inside
-- statement:
--   The ULHC construction uses the deg zero of inside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L415-L421
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L415-L421

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.deg_zero_of_inside {V : Finset Pt} {F : Finset Edge} (hV : Inside V F) {z : Pt}
    (hz : z ∉ V) : deg F z = 0 := by sorry
