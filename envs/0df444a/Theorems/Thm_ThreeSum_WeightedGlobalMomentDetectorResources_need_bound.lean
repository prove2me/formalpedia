-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentDetectorResources_need_bound
-- name    : ThreeSum.WeightedGlobalMomentDetectorResources.need_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:25:32.381797+00:00
-- url     : https://prove2.me/theorems/b6fb852c-175f-4c32-b44a-de357fedef08
-- title:
--   Weighted Global Moment Detector Resources: need bound
-- statement:
--   The Weighted Global Moment Detector Resources construction uses the need bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L45-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L45-L60

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
import Theorems.Thm_ThreeSum_WeightedFrontendResources_need_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds

theorem ThreeSum.WeightedGlobalMomentDetectorResources.need_bound (B U H : ℕ) :
    (need B U H).word≤coefficient B H*(U+1)^degree H ∧
    (need B U H).cells≤coefficient B H*(U+1)^degree H ∧
    (need B U H).depth≤coefficient B H*(U+1)^degree H := by sorry
