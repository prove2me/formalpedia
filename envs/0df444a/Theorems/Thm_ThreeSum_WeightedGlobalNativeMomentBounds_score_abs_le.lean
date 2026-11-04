-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_score_abs_le
-- name    : ThreeSum.WeightedGlobalNativeMomentBounds.score_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:06:58.359853+00:00
-- url     : https://prove2.me/theorems/52e5dff8-56dc-40d3-ab7c-3db948988ac1
-- title:
--   Weighted Global Native Moment Bounds: score abs le
-- statement:
--   The Weighted Global Native Moment Bounds construction uses the score abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L131-L165
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L131-L165

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem ThreeSum.WeightedGlobalNativeMomentBounds.score_abs_le {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (k j i : ℕ)
    (hL : ∀ a<S.left.NL, |LightWeightedGlobalMomentChannelFactory.leftWeights k j B a|≤(S.left.weightU : ℤ))
    (hR : ∀ a<S.right.NL, |LightWeightedGlobalMomentChannelFactory.rightWeights k j C a|≤(S.right.weightU : ℤ)) :
    |LightWeightedGlobalMomentChannelFactory.score S B C k j i|≤(scoreBound S : ℤ) := by sorry
