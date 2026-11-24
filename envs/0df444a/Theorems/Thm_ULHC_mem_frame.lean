-- Prove2me | Theorems.Thm_ULHC_mem_frame
-- name    : ULHC.mem_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:08:08.91812+00:00
-- url     : https://prove2.me/theorems/57723bf8-5373-4018-95b0-2676ff3958f9
-- title:
--   ULHC: mem frame
-- statement:
--   The ULHC construction uses the mem frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L342-L344
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L342-L344

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.mem_frame (z : Pt) (tf : Side) {y : Edge}
    (hy : y = lat1 z tf ∨ y = lat2 z tf ∨ y = back z tf ∨ y = front z tf) : y ∈ cellE z := by sorry
