-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrefixSetupResources_depth_powerBound
-- name    : ThreeSum.WeightedGlobalPrefixSetupResources.depth_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:51:26.578459+00:00
-- url     : https://prove2.me/theorems/54ff275d-2325-4ee1-a562-e7ff63f345ae
-- title:
--   Weighted Global Prefix Setup Resources: depth power Bound
-- statement:
--   The Weighted Global Prefix Setup Resources construction uses the depth power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSetupResources.lean#L104-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSetupResources.lean#L104-L106

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

theorem ThreeSum.WeightedGlobalPrefixSetupResources.depth_powerBound {m : ℕ} (hm : 0<m) (F : ℕ) :
    PowerBound (fun n=>(need m (radixLength m n) F).depth) 0 := by sorry
