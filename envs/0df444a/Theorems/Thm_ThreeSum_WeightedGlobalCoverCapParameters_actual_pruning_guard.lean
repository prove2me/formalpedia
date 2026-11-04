-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_actual_pruning_guard
-- name    : ThreeSum.WeightedGlobalCoverCapParameters.actual_pruning_guard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:00:50.84693+00:00
-- url     : https://prove2.me/theorems/5dabd9bd-aa50-4841-b2b9-972c632aefd7
-- title:
--   Weighted Global Cover Cap Parameters: actual pruning guard
-- statement:
--   The Weighted Global Cover Cap Parameters construction uses the actual pruning guard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverCapParameters.lean#L70-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverCapParameters.lean#L70-L76

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalCoverCapParameters
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency WeightedGlobalPartitionCount TernaryTypeLowerBound

theorem ThreeSum.WeightedGlobalCoverCapParameters.actual_pruning_guard (m p B k : ℕ) (hk : 0 < k) :
    16*p^4*B^2*3^(4*k^2) ≤ rawThreshold p B k ^ k*Fintype.card (ActualEdge m) := by sorry
