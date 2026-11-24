-- Prove2me | Theorems.Thm_ULHC_Ends_ne_at
-- name    : ULHC.Ends.ne_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:17:46.946485+00:00
-- url     : https://prove2.me/theorems/bf51762e-2dd5-4a23-9360-a09aaaabc1f7
-- title:
--   Ends: ne at
-- statement:
--   The Ends construction uses the ne at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Stacked.lean#L56-L62
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Stacked.lean#L56-L62

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.Ends.ne_at {g g' : Edge} {x m m' : Pt} (h : Ends g x m) (h' : Ends g' m m')
    (hx : x ≠ m') : g ≠ g' := by sorry
