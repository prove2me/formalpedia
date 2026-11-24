-- Prove2me | Theorems.Thm_ULHC_isCell_corners
-- name    : ULHC.isCell_corners
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:22.699227+00:00
-- url     : https://prove2.me/theorems/e1700cc6-cdd4-46d8-97e5-40afdc149940
-- title:
--   ULHC: is Cell corners
-- statement:
--   The ULHC construction uses the is Cell corners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L386-L391
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L386-L391

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.isCell_corners {V : Finset Pt} {c : Pt} (h : IsCell V c) (s : Side) :
    back1 c s ∈ V ∧ back2 c s ∈ V ∧ front1 c s ∈ V ∧ front2 c s ∈ V := by sorry
