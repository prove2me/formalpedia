-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_J_le
-- name    : ThreeSum.LightWeightedGlobalDimensions.J_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:39:02.7958+00:00
-- url     : https://prove2.me/theorems/0fdf9b5d-23e0-4328-b503-77dca7343dc5
-- title:
--   Light Weighted Global Dimensions: J le
-- statement:
--   The Light Weighted Global Dimensions construction uses the J le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsBudget.lean#L24-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsBudget.lean#L24-L28

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

theorem ThreeSum.LightWeightedGlobalDimensions.J_le {M b : ℕ} (hM : 1<M) (hb : 1<b) (n U : ℕ) : J M b n U≤n^2+4*U+3 := by sorry
