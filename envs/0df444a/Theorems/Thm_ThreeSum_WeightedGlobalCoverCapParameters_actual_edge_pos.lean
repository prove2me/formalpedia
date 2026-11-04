-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_actual_edge_pos
-- name    : ThreeSum.WeightedGlobalCoverCapParameters.actual_edge_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:58.623204+00:00
-- url     : https://prove2.me/theorems/f94c83da-9334-49b0-ab11-67fec65118a8
-- title:
--   Weighted Global Cover Cap Parameters: actual edge pos
-- statement:
--   The Weighted Global Cover Cap Parameters construction uses the actual edge pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverCapParameters.lean#L59-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverCapParameters.lean#L59-L68

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalCoverCapParameters
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency WeightedGlobalPartitionCount TernaryTypeLowerBound

theorem ThreeSum.WeightedGlobalCoverCapParameters.actual_edge_pos (m : ℕ) : 0 < Fintype.card (ActualEdge m) := by sorry
