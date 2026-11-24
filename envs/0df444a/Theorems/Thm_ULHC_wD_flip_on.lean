-- Prove2me | Theorems.Thm_ULHC_wD_flip_on
-- name    : ULHC.wD_flip_on
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:10.331813+00:00
-- url     : https://prove2.me/theorems/9355865a-fd58-47e7-88e6-090ddb31c0b9
-- title:
--   ULHC: w D flip on
-- statement:
--   The ULHC construction uses the w D flip on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L232-L240
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L232-L240

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.wD_flip_on {F H : Finset Edge} {c : Pt} {e : Edge} (he : e ∈ cellE c) :
    wD (flip F c) H e - wD F H e = - (if up F e then 2 else -2) := by sorry
