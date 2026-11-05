-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentChannelResources_score_abs_le
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentChannelResources.score_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:44:01.257683+00:00
-- url     : https://prove2.me/theorems/1327a5a3-7ca1-4a1d-82bf-4ec2b6bccefe
-- title:
--   score_abs_le
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentChannelResources.lean#L24-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentChannelResources.lean#L24-L36

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDetectorResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentChannelResources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeMomentBounds_score_abs_le

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentChannelResources
open WeightedGlobalMomentWeightBounds WeightedGlobalNativeMomentBounds StageBounds

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentChannelResources.score_abs_le {N B U K k j : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (left right : ℕ→ℤ) (hpairs : pairBound S*2^N≤B)
    (hleft : ∀ i<S.left.NL, |left i|≤(U : ℤ))
    (hright : ∀ i<S.right.NL, |right i|≤(U : ℤ)) (hk : k≤K) (hj : j≤k) (i : ℕ) :
    |LightWeightedGlobalMomentChannelFactory.score S left right k j i|≤(scoreBound B U K : ℤ) := by sorry
