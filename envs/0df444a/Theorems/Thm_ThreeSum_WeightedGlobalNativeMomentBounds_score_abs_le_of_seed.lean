-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_score_abs_le_of_seed
-- name    : ThreeSum.WeightedGlobalNativeMomentBounds.score_abs_le_of_seed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:06:50.370193+00:00
-- url     : https://prove2.me/theorems/aed93ef8-aafa-425f-ab9c-bd99bba87ba1
-- title:
--   Weighted Global Native Moment Bounds: score abs le of seed
-- statement:
--   The Weighted Global Native Moment Bounds construction uses the score abs le of seed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L167-L173
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L167-L173

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem ThreeSum.WeightedGlobalNativeMomentBounds.score_abs_le_of_seed {N d boundary : ℕ} {lim : Light.Limits}
    (S : WeightedSourceCountExecutionFactory.Setup N) (μ : ℕ→ℤ) (B C : ℕ→ℤ) (k j i : ℕ)
    (H : WeightedSourceCountExecutionFactory.Seed S lim d boundary μ
      (LightWeightedGlobalMomentChannelFactory.leftWeights k j B)
      (LightWeightedGlobalMomentChannelFactory.rightWeights k j C)) :
    |LightWeightedGlobalMomentChannelFactory.score S B C k j i|≤(scoreBound S : ℤ) := by sorry
