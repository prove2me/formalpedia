-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentChannelResources_score_abs_le
-- name    : ThreeSum.WeightedGlobalMomentChannelResources.score_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:48:23.371783+00:00
-- url     : https://prove2.me/theorems/db182117-3a50-4c68-b80d-4fc46c5d516c
-- title:
--   Weighted Global Moment Channel Resources: score abs le
-- statement:
--   The Weighted Global Moment Channel Resources construction uses the score abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentChannelResources.lean#L24-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentChannelResources.lean#L24-L36

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_score_abs_le

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentChannelResources
open WeightedGlobalMomentWeightBounds WeightedGlobalNativeMomentBounds StageBounds

theorem ThreeSum.WeightedGlobalMomentChannelResources.score_abs_le {N B U K k j : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (left right : ℕ→ℤ) (hpairs : pairBound S*2^N≤B)
    (hleft : ∀ i<S.left.NL, |left i|≤(U : ℤ))
    (hright : ∀ i<S.right.NL, |right i|≤(U : ℤ)) (hk : k≤K) (hj : j≤k) (i : ℕ) :
    |LightWeightedGlobalMomentChannelFactory.score S left right k j i|≤(scoreBound B U K : ℤ) := by sorry
