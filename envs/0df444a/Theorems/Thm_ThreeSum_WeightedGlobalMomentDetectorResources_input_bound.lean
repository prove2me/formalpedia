-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentDetectorResources_input_bound
-- name    : ThreeSum.WeightedGlobalMomentDetectorResources.input_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:25:13.21261+00:00
-- url     : https://prove2.me/theorems/6e93d718-7d66-4ba5-b56d-86cbf2e6af55
-- title:
--   Weighted Global Moment Detector Resources: input bound
-- statement:
--   The Weighted Global Moment Detector Resources construction uses the input bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L29-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L29-L43

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds

theorem ThreeSum.WeightedGlobalMomentDetectorResources.input_bound (B U H : ℕ) :
    input B U H+1≤(B*2^(2*H)+1)*(U+1)^(2*H+1) := by sorry
