-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentChannelResources_polyNeed
-- name    : ThreeSum.WeightedGlobalMomentChannelResources.polyNeed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:07:37.377804+00:00
-- url     : https://prove2.me/theorems/687e1935-2fe3-4513-bd95-05b0cecd5c32
-- title:
--   Weighted Global Moment Channel Resources: poly Need
-- statement:
--   The Weighted Global Moment Channel Resources construction uses the poly Need property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentChannelResources.lean#L91-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentChannelResources.lean#L91-L105

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Theorems.Thm_ThreeSum_WeightedFrontendResources_polyNeed
import Theorems.Thm_ThreeSum_WeightedGlobalMomentDetectorResources_polyNeed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentChannelResources
open WeightedGlobalMomentWeightBounds WeightedGlobalNativeMomentBounds StageBounds

theorem ThreeSum.WeightedGlobalMomentChannelResources.polyNeed {B : ℕ→ℕ} {a : ℝ} (hB : PowerBound B a) (K : ℕ) :
    Light.PolyNeed (fun n U => need (B n) U K) := by sorry
