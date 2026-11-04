-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_controls
-- name    : ThreeSum.WeightedGlobalFrontendResources.controls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:22:44.034974+00:00
-- url     : https://prove2.me/theorems/29f6cd3d-e916-41e4-ba4c-2fffa9a40f21
-- title:
--   Weighted Global Frontend Resources: controls
-- statement:
--   The Weighted Global Frontend Resources construction uses the controls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L71-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L71-L87

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

theorem ThreeSum.WeightedGlobalFrontendResources.controls (N nb groups count R A : ℕ) :
    nb+R+2^(2*N+1)+1025*N+1100≤ word N nb groups count R A ∧
    1026*N+R+1200≤ word N nb groups count R A ∧
    4*eulerBound N A+8*N+16≤ word N nb groups count R A ∧
    4^(N+1)≤ word N nb groups count R A ∧
    4*sourceZeta N A+3≤ word N nb groups count R A ∧
    (sourceZeta N A)^2≤ word N nb groups count R A ∧
    4*4^N*(sourceZeta N A)^2+3≤ word N nb groups count R A ∧
    groups+1≤ word N nb groups count R A ∧
    count+1≤ word N nb groups count R A := by sorry
