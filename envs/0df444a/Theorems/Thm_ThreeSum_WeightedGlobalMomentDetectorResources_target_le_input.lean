-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentDetectorResources_target_le_input
-- name    : ThreeSum.WeightedGlobalMomentDetectorResources.target_le_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:30:14.363207+00:00
-- url     : https://prove2.me/theorems/0157e5d8-de1f-402f-8c7c-490b98fb60f7
-- title:
--   Weighted Global Moment Detector Resources: target le input
-- statement:
--   The Weighted Global Moment Detector Resources construction uses the target le input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L119-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L119-L121

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds

theorem ThreeSum.WeightedGlobalMomentDetectorResources.target_le_input (B U H : ℕ) (x : ℤ) (hx : |x|≤(U : ℤ)) :
    |x|≤(input B U H : ℤ) := by sorry
