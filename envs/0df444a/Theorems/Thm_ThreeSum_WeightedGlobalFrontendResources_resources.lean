-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_resources
-- name    : ThreeSum.WeightedGlobalFrontendResources.resources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:29:36.512871+00:00
-- url     : https://prove2.me/theorems/c2ac9883-968f-44e4-b681-b0347b52b338
-- title:
--   Weighted Global Frontend Resources: resources
-- statement:
--   The two metadata matrices, memo values, and division scratch have a
--   literal layout. The division reserve uses `V+3`, a conservative polynomial
--   upper bound on the actual logarithmic table length.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L111-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L111-L166

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


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

theorem ThreeSum.WeightedGlobalFrontendResources.resources {lim : Limits} {a N R A bank nb bv T h ws rows groups count : ℕ}
    (hrows : rows≤ R) (hCut : T≤1025*N) (hT : h≤2*N) (hh : 1025*h≤2*T)
    (hnb : nb< 2^(2*N)) (hnn : rows< 2^(2*N)) (hpos : 0< nb)
    (hbank : bank+nb≤ a) (hbv : bv+nb≤ a)
    (hstart : powers a N R+(2*N+1)≤ ws)
    (hend : division ws N R+eulerBound N A+3≤ lim.space)
    (hw : (lim.space:ℤ)≤ lim.word)
    (hword : (word N nb groups count R A:ℤ)≤ lim.word)
    (F : TritWord N→ ℤ) (hhom : ∀ W, F W≠ 0→ rank W=h)
    (hF : ∀ W, |F W|≤ (A:ℤ)) :
    Resources lim rows (config a N R A bank nb bv T h ws) F := by sorry
