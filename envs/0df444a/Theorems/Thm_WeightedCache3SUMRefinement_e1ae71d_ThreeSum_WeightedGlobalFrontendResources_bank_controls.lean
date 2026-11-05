-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFrontendResources_bank_controls
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFrontendResources.bank_controls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:19:22.145707+00:00
-- url     : https://prove2.me/theorems/1c7134dd-361f-4aab-b837-a83fca0cfb48
-- title:
--   bank_controls
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/FrontendResources.lean#L89-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/FrontendResources.lean#L89-L99

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_FrontendResources
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.WeightedGlobalBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFrontendResources.bank_controls (N nb groups count R A : ℕ) :
    nb+2^(2*N+1)+16≤word N nb groups count R A ∧
    2*N+3≤word N nb groups count R A ∧
    (N+1)*nb≤word N nb groups count R A ∧
    N*nb≤word N nb groups count R A ∧
    4*(4^N*A)+3≤word N nb groups count R A ∧
    LightWeightedBankAssembly.valueBound N A≤word N nb groups count R A ∧
    4*(4^N*LightWeightedBankAssembly.valueBound N A)+3≤word N nb groups count R A := by sorry
