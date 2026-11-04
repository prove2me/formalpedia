-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrefixSetupResources_need_ok
-- name    : ThreeSum.WeightedGlobalPrefixSetupResources.need_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:49:22.370076+00:00
-- url     : https://prove2.me/theorems/24d36f26-7304-4ae7-9232-92f333db5e34
-- title:
--   Weighted Global Prefix Setup Resources: need ok
-- statement:
--   The Weighted Global Prefix Setup Resources construction uses the need ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSetupResources.lean#L25-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSetupResources.lean#L25-L33

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSetupResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrefixSetupResources
open Light LightWeightedGlobalPrefixSetup StageBounds WeightedGlobalCoverScale
open WeightedGlobalFrontendResources
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

theorem ThreeSum.WeightedGlobalPrefixSetupResources.need_ok {lim : Limits} {m j F free d : ℕ}
    (H : (need m j F).Ok lim free d) :
    endAt free m j≤ lim.space ∧ (LightWeightedGlobalPrefixSetup.word m j F:ℤ)≤ lim.word ∧
      d+N m j+4≤ lim.depth := by sorry
