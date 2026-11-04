-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_time_linear_parameters
-- name    : ThreeSum.LightWeightedGlobalDimensions.time_linear_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:43:37.611275+00:00
-- url     : https://prove2.me/theorems/19481e4e-6014-4218-94dd-8f1d2403d1af
-- title:
--   Light Weighted Global Dimensions: time linear parameters
-- statement:
--   The Light Weighted Global Dimensions construction uses the time linear parameters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsTime.lean#L16-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsTime.lean#L16-L26

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsTime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalDimensions
open WeightedGlobalSignedPadding TernaryExtensionEncoding WeightedGlobalCoverScale Filter Real
set_option maxHeartbeats 2000000

theorem ThreeSum.LightWeightedGlobalDimensions.time_linear_parameters (M b p K n U : ℕ) :
    time M b p K n U ≤ 1000*(p^(dim M b p K n U)+dim M b p K n U+J M b n U+3) := by sorry
