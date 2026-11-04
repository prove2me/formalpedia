-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrontendResources_heapEnd_eq
-- name    : ThreeSum.WeightedFrontendResources.heapEnd_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:26:30.724484+00:00
-- url     : https://prove2.me/theorems/3c18997a-3d91-41d0-b7eb-44fabdd2b411
-- title:
--   Weighted Frontend Resources: heap End eq
-- statement:
--   The Weighted Frontend Resources construction uses the heap End eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrontendResources.lean#L56-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrontendResources.lean#L56-L59

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

theorem ThreeSum.WeightedFrontendResources.heapEnd_eq (a N R A : ℕ) :
    heapEnd a N R A=a+(4*N+6)*R+6*N+2*eulerBound N A+7 := by sorry
