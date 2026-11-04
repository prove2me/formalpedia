-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrontendResources_fixed_radix_powerBound
-- name    : ThreeSum.WeightedFrontendResources.fixed_radix_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:28:54.220308+00:00
-- url     : https://prove2.me/theorems/4b5bcba5-0a4e-44b9-9dd3-c71e1bfec126
-- title:
--   Weighted Frontend Resources: fixed radix power Bound
-- statement:
--   Every fixed native alphabet, occurrence-map family, carry alphabet, or
--   bit-mask base raised to the actual number of prefixes is polynomial.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrontendResources.lean#L356-L373
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrontendResources.lean#L356-L373

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_FrontendResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
open ThreeSum.TernaryCoverScale ThreeSum.TernaryPrincipalDimensions

theorem ThreeSum.WeightedFrontendResources.fixed_radix_powerBound {m : ℕ} (hm : 0< m) (b : ℕ) :
    PowerBound (fun n=>(b+1)^radixLength m n)
      (2*Real.log (b+1:ℕ)/Real.log (outputSize m:ℝ)) := by sorry
