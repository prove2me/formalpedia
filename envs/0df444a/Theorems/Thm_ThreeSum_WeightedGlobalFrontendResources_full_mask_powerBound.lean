-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_full_mask_powerBound
-- name    : ThreeSum.WeightedGlobalFrontendResources.full_mask_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:27:40.437704+00:00
-- url     : https://prove2.me/theorems/6cf7c8aa-5b39-450b-bfc6-445b111c4ad3
-- title:
--   Weighted Global Frontend Resources: full mask power Bound
-- statement:
--   The Weighted Global Frontend Resources construction uses the full mask power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L396-L408
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L396-L408

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_FrontendResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.WeightedGlobalBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
open ThreeSum.WeightedGlobalCoverScale ThreeSum.WeightedGlobalPrincipalDimensions

theorem ThreeSum.WeightedGlobalFrontendResources.full_mask_powerBound {m : ℕ} (hm : 0< m) :
    PowerBound (fun n=>4^WeightedGlobalLocalParameters.fixedLength (radixLength m n*m))
      (2*Real.log (4^WeightedGlobalLocalParameters.fixedLength m:ℕ)/Real.log (outputSize m:ℝ)) := by sorry
