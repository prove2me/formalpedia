-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_word_linear_bound
-- name    : ThreeSum.LightWeightedGlobalDimensions.word_linear_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:44:50.391708+00:00
-- url     : https://prove2.me/theorems/5422d0c9-edfb-49f3-bd29-d999aca00598
-- title:
--   Light Weighted Global Dimensions: word linear bound
-- statement:
--   The Light Weighted Global Dimensions construction uses the word linear bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsBudget.lean#L30-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsBudget.lean#L30-L72

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

theorem ThreeSum.LightWeightedGlobalDimensions.word_linear_bound {M b p K : ℕ} [Fact p.Prime]
    (hM : 1<M) (hb : 1<b) (n U : ℕ) :
    word M b p K n U≤1000*(coefficientBase M b p K)^2*(n^2+4*U+3) := by sorry
