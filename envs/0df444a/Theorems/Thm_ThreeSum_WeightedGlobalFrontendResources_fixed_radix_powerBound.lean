-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_fixed_radix_powerBound
-- name    : ThreeSum.WeightedGlobalFrontendResources.fixed_radix_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:25:08.713177+00:00
-- url     : https://prove2.me/theorems/f9efef55-e5af-4b56-8260-04198b92ece8
-- title:
--   Weighted Global Frontend Resources: fixed radix power Bound
-- statement:
--   Every fixed native alphabet, occurrence-map family, carry alphabet, or
--   bit-mask base raised to the actual number of prefixes is polynomial.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L362-L379
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L362-L379

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

theorem ThreeSum.WeightedGlobalFrontendResources.fixed_radix_powerBound {m : ℕ} (hm : 0< m) (b : ℕ) :
    PowerBound (fun n=>(b+1)^radixLength m n)
      (2*Real.log (b+1:ℕ)/Real.log (outputSize m:ℝ)) := by sorry
