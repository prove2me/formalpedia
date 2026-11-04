-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrontendResources_controls
-- name    : ThreeSum.WeightedFrontendResources.controls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:22:52.045062+00:00
-- url     : https://prove2.me/theorems/4e7d652f-5aa1-45ab-b183-60afa18d7cb4
-- title:
--   Weighted Frontend Resources: controls
-- statement:
--   The Weighted Frontend Resources construction uses the controls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrontendResources.lean#L65-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrontendResources.lean#L65-L81

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

theorem ThreeSum.WeightedFrontendResources.controls (N nb groups count R A : ℕ) :
    nb+R+2^(2*N+1)+1025*N+1100≤ word N nb groups count R A ∧
    1026*N+R+1200≤ word N nb groups count R A ∧
    4*eulerBound N A+8*N+16≤ word N nb groups count R A ∧
    4^(N+1)≤ word N nb groups count R A ∧
    4*sourceZeta N A+3≤ word N nb groups count R A ∧
    (sourceZeta N A)^2≤ word N nb groups count R A ∧
    4*4^N*(sourceZeta N A)^2+3≤ word N nb groups count R A ∧
    groups+1≤ word N nb groups count R A ∧
    count+1≤ word N nb groups count R A := by sorry
