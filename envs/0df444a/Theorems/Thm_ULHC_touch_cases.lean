-- Prove2me | Theorems.Thm_ULHC_touch_cases
-- name    : ULHC.touch_cases
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:17:54.475815+00:00
-- url     : https://prove2.me/theorems/15f423b6-2943-40c6-b97b-892e15ae7a2b
-- title:
--   ULHC: touch cases
-- statement:
--   The ULHC construction uses the touch cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearGeo.lean#L31-L49
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearGeo.lean#L31-L49

import Definitions.Def_ULHC_Touch
import Definitions.Def_ULHC_Stacked
import Definitions.Def_ULHC_NearGeo
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.touch_cases {q d : Pt} (s : Side) {x : Edge} (h1 : x ∈ cellE q) (h2 : x ∈ cellE d) :
    q = d ∨ q = nb d s ∨ q = nb d s.opp ∨ q = nb d (latA s) ∨ q = nb d (latB s) := by sorry
