-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_heapEnd_eq
-- name    : ThreeSum.WeightedGlobalFrontendResources.heapEnd_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:26:36.673236+00:00
-- url     : https://prove2.me/theorems/5b63aba3-ab15-4069-bca5-99409aa15542
-- title:
--   Weighted Global Frontend Resources: heap End eq
-- statement:
--   The Weighted Global Frontend Resources construction uses the heap End eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L62-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L62-L65

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

theorem ThreeSum.WeightedGlobalFrontendResources.heapEnd_eq (a N R A : ℕ) :
    heapEnd a N R A=a+(4*N+6)*R+6*N+2*eulerBound N A+7 := by sorry
