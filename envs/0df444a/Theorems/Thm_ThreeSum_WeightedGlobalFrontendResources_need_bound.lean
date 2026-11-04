-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_need_bound
-- name    : ThreeSum.WeightedGlobalFrontendResources.need_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:27:35.775197+00:00
-- url     : https://prove2.me/theorems/548bcdc0-2983-47f7-a071-c42090741958
-- title:
--   Weighted Global Frontend Resources: need bound
-- statement:
--   An explicit polynomial in the literal dimensions and source magnitudes.
--   It bounds the actual workspace, all scalar words, and recursive depth.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L256-L316
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L256-L316

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

theorem ThreeSum.WeightedGlobalFrontendResources.need_bound {N nb groups count R A priorCells hostWord B : ℕ}
    (hN : N≤ B) (hnb : nb≤ B) (hgroups : groups≤ B) (hcount : count≤ B)
    (hR : R≤ B) (hA : A≤ B) (hprior : priorCells≤ B) (hhost : hostWord≤ B)
    (hfour : 4^N≤ B) :
    (need N nb groups count R A priorCells hostWord).word≤ envelope B ∧
    (need N nb groups count R A priorCells hostWord).cells≤ envelope B ∧
    (need N nb groups count R A priorCells hostWord).depth≤ envelope B := by sorry
