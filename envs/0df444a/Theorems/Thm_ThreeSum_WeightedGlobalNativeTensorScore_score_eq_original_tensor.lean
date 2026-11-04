-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeTensorScore_score_eq_original_tensor
-- name    : ThreeSum.WeightedGlobalNativeTensorScore.score_eq_original_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:07:47.658549+00:00
-- url     : https://prove2.me/theorems/69abbd04-485f-4eee-9fad-c28db1280d24
-- title:
--   Weighted Global Native Tensor Score: score eq original tensor
-- statement:
--   The Weighted Global Native Tensor Score construction uses the score eq original tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTensorScore.lean#L66-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTensorScore.lean#L66-L79

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeTensorScore
open TernaryJointType WeightedGlobalNativePairMoments
open LightWeightedGlobalTensorFactory LightTernaryPairedPolynomial
open scoped BigOperators
set_option maxHeartbeats 1500000

theorem ThreeSum.WeightedGlobalNativeTensorScore.score_eq_original_tensor {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (J : ℕ) (L R : ℕ→ℕ→ℤ) (i : ℕ) (a b c d : Fin (J+2)) :
    score S J L R i (tensorIndex (J+2) a.val b.val c.val d.val)=
      TernaryConvolution.factorial (S.front.Q i)*
        TernaryPairedTensor.tensor (originalLeft S J L i) (originalRight S J R i) a b c d := by sorry
