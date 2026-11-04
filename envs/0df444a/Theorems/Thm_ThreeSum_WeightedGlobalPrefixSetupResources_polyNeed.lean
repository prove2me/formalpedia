-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrefixSetupResources_polyNeed
-- name    : ThreeSum.WeightedGlobalPrefixSetupResources.polyNeed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:29:17.927547+00:00
-- url     : https://prove2.me/theorems/7afdf427-c9da-4de1-9a4f-f639a80c37c7
-- title:
--   Weighted Global Prefix Setup Resources: poly Need
-- statement:
--   The Weighted Global Prefix Setup Resources construction uses the poly Need property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSetupResources.lean#L108-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSetupResources.lean#L108-L112

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSetupResources
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_polyNeed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrefixSetupResources
open Light LightWeightedGlobalPrefixSetup StageBounds WeightedGlobalCoverScale
open WeightedGlobalFrontendResources
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

theorem ThreeSum.WeightedGlobalPrefixSetupResources.polyNeed {m : ℕ} (hm : 0<m) (F : ℕ) :
    Light.PolyNeed (fun n _U=>need m (radixLength m n) F) := by sorry
