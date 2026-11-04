-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrefixSetupResources_need_mono_prefix
-- name    : ThreeSum.WeightedGlobalPrefixSetupResources.need_mono_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:58:05.952255+00:00
-- url     : https://prove2.me/theorems/64ecc19e-a031-4610-8b44-524090fb4356
-- title:
--   Weighted Global Prefix Setup Resources: need mono prefix
-- statement:
--   The Weighted Global Prefix Setup Resources construction uses the need mono prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSetupResources.lean#L46-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSetupResources.lean#L46-L55

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

theorem ThreeSum.WeightedGlobalPrefixSetupResources.need_mono_prefix {m j r F : ℕ} (hjr : j≤ r) :
    (need m j F).word≤ (need m r F).word ∧
    (need m j F).cells≤ (need m r F).cells ∧
    (need m j F).depth≤ (need m r F).depth := by sorry
