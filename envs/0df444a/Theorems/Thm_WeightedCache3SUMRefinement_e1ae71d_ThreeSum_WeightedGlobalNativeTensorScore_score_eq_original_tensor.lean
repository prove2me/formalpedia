-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeTensorScore_score_eq_original_tensor
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeTensorScore.score_eq_original_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:22:40.227475+00:00
-- url     : https://prove2.me/theorems/924491a8-60bb-46d9-a798-4a324cd390cb
-- title:
--   score_eq_original_tensor
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeTensorScore.lean#L66-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeTensorScore.lean#L66-L79

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTensorScore
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeTensorScore
open TernaryJointType WeightedGlobalNativePairMoments
open LightWeightedGlobalTensorFactory LightTernaryPairedPolynomial
open scoped BigOperators
set_option maxHeartbeats 1500000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeTensorScore.score_eq_original_tensor {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (J : ℕ) (L R : ℕ→ℕ→ℤ) (i : ℕ) (a b c d : Fin (J+2)) :
    score S J L R i (tensorIndex (J+2) a.val b.val c.val d.val)=
      TernaryConvolution.factorial (S.front.Q i)*
        TernaryPairedTensor.tensor (originalLeft S J L i) (originalRight S J R i) a b c d := by sorry
