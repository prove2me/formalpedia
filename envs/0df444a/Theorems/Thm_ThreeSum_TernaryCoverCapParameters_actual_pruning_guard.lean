-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverCapParameters_actual_pruning_guard
-- name    : ThreeSum.TernaryCoverCapParameters.actual_pruning_guard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:21.04979+00:00
-- url     : https://prove2.me/theorems/b6ee7740-f635-4fef-8707-8429d446eb4c
-- title:
--   Ternary Cover Cap Parameters: actual pruning guard
-- statement:
--   The Ternary Cover Cap Parameters construction uses the actual pruning guard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverCapParameters.lean#L63-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverCapParameters.lean#L63-L69

import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverCapParameters
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps TernaryCoverFrequency TernaryPartitionCount TernaryTypeLowerBound

theorem ThreeSum.TernaryCoverCapParameters.actual_pruning_guard (m p B k : ℕ) (hk : 0 < k) :
    16*p^4*B^2*3^(4*k^2) ≤ rawThreshold p B k ^ k*Fintype.card (ActualEdge m) := by sorry
