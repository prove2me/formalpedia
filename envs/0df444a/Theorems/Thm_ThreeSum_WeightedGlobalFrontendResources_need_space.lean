-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_need_space
-- name    : ThreeSum.WeightedGlobalFrontendResources.need_space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:53:31.181426+00:00
-- url     : https://prove2.me/theorems/c2f760e3-3d13-45fa-9e2f-45c67b9ec022
-- title:
--   Weighted Global Frontend Resources: need space
-- statement:
--   The Weighted Global Frontend Resources construction uses the need space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L168-L175
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L168-L175

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

theorem ThreeSum.WeightedGlobalFrontendResources.need_space {lim : Limits} {free d N nb groups count R A priorCells hostWord : ℕ}
    (H : (need N nb groups count R A priorCells hostWord).Ok lim free d) :
    heapEnd (free+priorCells) N R A≤ lim.space ∧
    (word N nb groups count R A:ℤ)≤ lim.word ∧ d+5*N+16≤ lim.depth := by sorry
