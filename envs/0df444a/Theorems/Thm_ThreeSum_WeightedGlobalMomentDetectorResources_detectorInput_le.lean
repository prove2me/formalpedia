-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentDetectorResources_detectorInput_le
-- name    : ThreeSum.WeightedGlobalMomentDetectorResources.detectorInput_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:25:36.01743+00:00
-- url     : https://prove2.me/theorems/9711b105-ca4a-4f2a-b35d-53afe75ecab6
-- title:
--   Weighted Global Moment Detector Resources: detector Input le
-- statement:
--   The envelope coefficient is the literal-pair count times the actual
--   factorial mass bound. No support oracle is used for arithmetic bounds.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L101-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L101-L105

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds

theorem ThreeSum.WeightedGlobalMomentDetectorResources.detectorInput_le {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (B U H : ℕ) (hpairs : pairBound S*2^N≤B) :
    detectorInput S U H ≤ input B U H := by sorry
