-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentDetectorResources_polyNeed
-- name    : ThreeSum.WeightedGlobalMomentDetectorResources.polyNeed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:25:07.647642+00:00
-- url     : https://prove2.me/theorems/085ca6b5-c83e-4fae-88ba-89c60bdcde79
-- title:
--   Weighted Global Moment Detector Resources: poly Need
-- statement:
--   The Weighted Global Moment Detector Resources construction uses the poly Need property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L62-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L62-L97

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
import Theorems.Thm_ThreeSum_WeightedFrontendResources_polyNeed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds

theorem ThreeSum.WeightedGlobalMomentDetectorResources.polyNeed {B : ℕ→ℕ} {a : ℝ} (hB : PowerBound B a) (H : ℕ) :
    Light.PolyNeed (fun n U => need (B n) U H) := by sorry
