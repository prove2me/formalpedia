-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_need_space
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources.need_space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:20:01.585111+00:00
-- url     : https://prove2.me/theorems/0169dacc-fb75-4f44-b771-4abfcec51361
-- title:
--   need_space
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrontendResources.lean#L162-L169
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrontendResources.lean#L162-L169

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrontendResources
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources.need_space {lim : Limits} {free d N nb groups count R A priorCells hostWord : ℕ}
    (H : (need N nb groups count R A priorCells hostWord).Ok lim free d) :
    heapEnd (free+priorCells) N R A≤ lim.space ∧
    (word N nb groups count R A:ℤ)≤ lim.word ∧ d+5*N+16≤ lim.depth := by sorry
