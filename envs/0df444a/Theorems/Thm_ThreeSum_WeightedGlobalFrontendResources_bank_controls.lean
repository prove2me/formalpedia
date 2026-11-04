-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_bank_controls
-- name    : ThreeSum.WeightedGlobalFrontendResources.bank_controls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:30:33.237009+00:00
-- url     : https://prove2.me/theorems/eee00e86-83ea-4af2-be64-b689a7341866
-- title:
--   Weighted Global Frontend Resources: bank controls
-- statement:
--   The Weighted Global Frontend Resources construction uses the bank controls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L89-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L89-L99

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

theorem ThreeSum.WeightedGlobalFrontendResources.bank_controls (N nb groups count R A : ℕ) :
    nb+2^(2*N+1)+16≤word N nb groups count R A ∧
    2*N+3≤word N nb groups count R A ∧
    (N+1)*nb≤word N nb groups count R A ∧
    N*nb≤word N nb groups count R A ∧
    4*(4^N*A)+3≤word N nb groups count R A ∧
    LightWeightedBankAssembly.valueBound N A≤word N nb groups count R A ∧
    4*(4^N*LightWeightedBankAssembly.valueBound N A)+3≤word N nb groups count R A := by sorry
