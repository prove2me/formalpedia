-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentDetectorResources_moments_le_input
-- name    : ThreeSum.WeightedGlobalMomentDetectorResources.moments_le_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:25:29.71334+00:00
-- url     : https://prove2.me/theorems/dc74b50d-ea3e-4f3b-b843-45955de1030f
-- title:
--   Weighted Global Moment Detector Resources: moments le input
-- statement:
--   The Weighted Global Moment Detector Resources construction uses the moments le input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L107-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L107-L117

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds

theorem ThreeSum.WeightedGlobalMomentDetectorResources.moments_le_input {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (B U H : ℕ) (hpairs : pairBound S*2^N≤B) (left right : ℕ→ℤ)
    (hleft : ∀ j<S.left.NL, |left j|≤(U : ℤ))
    (hright : ∀ j<S.right.NL, |right j|≤(U : ℤ)) :
    ∀ i, ∀ k≤2*H,
      |∑ p : WeightedGlobalNativePairMoments.Pair S i,
        WeightedGlobalNativePairMoments.mass S i p*WeightedGlobalNativePairMoments.mode left right p^k|
        ≤(input B U H : ℤ) := by sorry
