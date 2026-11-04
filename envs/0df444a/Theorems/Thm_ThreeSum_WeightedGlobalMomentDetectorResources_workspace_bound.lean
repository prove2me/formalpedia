-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentDetectorResources_workspace_bound
-- name    : ThreeSum.WeightedGlobalMomentDetectorResources.workspace_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:26:23.823345+00:00
-- url     : https://prove2.me/theorems/358d9cbb-612d-443f-bb25-df9896654816
-- title:
--   Weighted Global Moment Detector Resources: workspace bound
-- statement:
--   The Weighted Global Moment Detector Resources construction uses the workspace bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L128-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean#L128-L131

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds

theorem ThreeSum.WeightedGlobalMomentDetectorResources.workspace_bound {count : ℕ} (B U H : ℕ) (hc : count≤B) :
    (2*H+1)*count+(2*H+1)≤(need B U H).cells := by sorry
