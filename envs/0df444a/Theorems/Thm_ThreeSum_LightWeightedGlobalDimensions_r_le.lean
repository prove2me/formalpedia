-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_r_le
-- name    : ThreeSum.LightWeightedGlobalDimensions.r_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:41:30.230467+00:00
-- url     : https://prove2.me/theorems/af245c7b-9504-4ea4-a7aa-7e789a9815c9
-- title:
--   Light Weighted Global Dimensions: r le
-- statement:
--   The Light Weighted Global Dimensions construction uses the r le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsBudget.lean#L21-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsBudget.lean#L21-L22

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalDimensions
open Light WeightedGlobalSignedPadding TernaryExtensionEncoding
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

theorem ThreeSum.LightWeightedGlobalDimensions.r_le {M : ℕ} (hM : 1<M) (n : ℕ) : r M n≤n^2 := by sorry
