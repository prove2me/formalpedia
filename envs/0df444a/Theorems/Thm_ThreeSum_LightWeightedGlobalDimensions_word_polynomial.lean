-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_word_polynomial
-- name    : ThreeSum.LightWeightedGlobalDimensions.word_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:41:22.307192+00:00
-- url     : https://prove2.me/theorems/8b62fd2d-661f-435f-807e-fe238fc8988c
-- title:
--   Light Weighted Global Dimensions: word polynomial
-- statement:
--   The Light Weighted Global Dimensions construction uses the word polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsBudget.lean#L74-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsBudget.lean#L74-L83

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

theorem ThreeSum.LightWeightedGlobalDimensions.word_polynomial {M b p K : ℕ} [Fact p.Prime]
    (hM : 1<M) (hb : 1<b) (n U : ℕ) :
    word M b p K n U≤coefficient M b p K*(n+1)^2*(U+1) := by sorry
