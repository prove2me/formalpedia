-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_rawThreshold_pos
-- name    : ThreeSum.WeightedGlobalCoverCapParameters.rawThreshold_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:32:38.62332+00:00
-- url     : https://prove2.me/theorems/f4d58d5c-82c0-4898-b87c-41e35b1b53ad
-- title:
--   Weighted Global Cover Cap Parameters: raw Threshold pos
-- statement:
--   The Weighted Global Cover Cap Parameters construction uses the raw Threshold pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverCapParameters.lean#L30-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverCapParameters.lean#L30-L30

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalCoverCapParameters
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency WeightedGlobalPartitionCount TernaryTypeLowerBound

theorem ThreeSum.WeightedGlobalCoverCapParameters.rawThreshold_pos (p B k : ℕ) : 0 < rawThreshold p B k := by sorry
