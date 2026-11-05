-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontendResources_resources
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontendResources.resources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:50:52.519227+00:00
-- url     : https://prove2.me/theorems/60bdd157-e554-4fdc-8b58-b6a5f2dbf7d5
-- title:
--   resources
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaFrontendResources.lean#L39-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaFrontendResources.lean#L39-L105

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_FrontendResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFrontendResources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFrontendResources_resources
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontendResources
open Light WeightedGlobalArenaLayout TernaryJointType WeightedGlobalBank TernaryEuler
open WeightedGlobalFrontendResources LightWeightedNearPair LightWeightedQueryPlan
open LightWeightedPreparedWanted WeightedBankStageModel TernaryCodeSemantics
set_option maxHeartbeats 6000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontendResources.resources {lim : Limits} {free C N R A bank nb bv T h wsSlot rows groups count : ℕ}
    (hws : wsSlot=58 ∨ wsSlot=62)
    (hrows : rows≤R) (hR : R≤C) (hN : N≤C) (hpowers : 2*N+1≤C)
    (hmetadata : 2*N*R+N≤C) (hdivision : eulerBound N A+3≤C)
    (hCut : T≤2740*N) (hT : h≤2*N) (hh : 2740*h≤2*T) (hnb : nb<2^(2*N)) (hnn : rows<2^(2*N)) (hpos : 0<nb)
    (hbank : bank+nb≤addr free C 54) (hbv : bv+nb≤addr free C 54)
    (hend : finish free C≤lim.space) (hw : (lim.space : ℤ)≤lim.word)
    (hword : (word N nb groups count R A : ℤ)≤lim.word)
    (F : TritWord N→ℤ) (hhom : ∀ W, F W≠0 → rank W=h)
    (hF : ∀ W, |F W|≤(A : ℤ)) :
    Resources lim rows (config free C N A bank nb bv T h wsSlot) F := by sorry
