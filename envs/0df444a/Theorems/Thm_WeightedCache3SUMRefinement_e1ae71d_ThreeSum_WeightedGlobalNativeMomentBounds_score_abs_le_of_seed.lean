-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeMomentBounds_score_abs_le_of_seed
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds.score_abs_le_of_seed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:22:08.82846+00:00
-- url     : https://prove2.me/theorems/8a767738-e649-411e-a19c-b29ddf05e956
-- title:
--   score_abs_le_of_seed
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L167-L173
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L167-L173

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeMomentBounds.score_abs_le_of_seed {N d boundary : ℕ} {lim : Light.Limits}
    (S : WeightedSourceCountExecutionFactory.Setup N) (μ : ℕ→ℤ) (B C : ℕ→ℤ) (k j i : ℕ)
    (H : WeightedSourceCountExecutionFactory.Seed S lim d boundary μ
      (LightWeightedGlobalMomentChannelFactory.leftWeights k j B)
      (LightWeightedGlobalMomentChannelFactory.rightWeights k j C)) :
    |LightWeightedGlobalMomentChannelFactory.score S B C k j i|≤(scoreBound S : ℤ) := by sorry
