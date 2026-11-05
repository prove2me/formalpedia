-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_resources
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources.resources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:27:43.935302+00:00
-- url     : https://prove2.me/theorems/e229c79f-2742-4b32-baef-3cf791b1ce80
-- title:
--   resources
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrontendResources.lean#L105-L160
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrontendResources.lean#L105-L160

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrontendResources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.rows


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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources.resources {lim : Limits} {a N R A bank nb bv T h ws rows groups count : ℕ}
    (hrows : rows≤ R) (hCut : T≤2740*N) (hT : h≤2*N) (hh : 2740*h≤2*T)
    (hnb : nb< 2^(2*N)) (hnn : rows< 2^(2*N)) (hpos : 0< nb)
    (hbank : bank+nb≤ a) (hbv : bv+nb≤ a)
    (hstart : powers a N R+(2*N+1)≤ ws)
    (hend : division ws N R+eulerBound N A+3≤ lim.space)
    (hw : (lim.space:ℤ)≤ lim.word)
    (hword : (word N nb groups count R A:ℤ)≤ lim.word)
    (F : TritWord N→ ℤ) (hhom : ∀ W, F W≠ 0→ rank W=h)
    (hF : ∀ W, |F W|≤ (A:ℤ)) :
    Resources lim rows (config a N R A bank nb bv T h ws) F := by sorry
