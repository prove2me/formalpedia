-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontendResources_plan
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontendResources.plan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:53:06.692337+00:00
-- url     : https://prove2.me/theorems/9917abb4-ef6f-4f5b-b4f4-5a20f5b6ce74
-- title:
--   plan
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaFrontendResources.lean#L107-L163
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaFrontendResources.lean#L107-L163

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_FrontendResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFrontendResources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFrontendResources_plan
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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFrontendResources.plan {lim : Limits} {free C N R A bank nb fbv gbv T fh gh bankValues groups count : ℕ}
    (Q : TritWord N) (E : Enumeration N T nb) (F G : TritWord N→ℤ)
    (hrows : rows Q T≤R) (hR : R≤C) (hN : N≤C) (hpowers : 2*N+1≤C)
    (hmetadata : 2*N*R+N≤C) (hdivision : eulerBound N A+3≤C)
    (hCut : T≤2740*N) (hfDegree : fh≤2*N) (hgDegree : gh≤2*N) (hfh : 2740*fh≤2*T) (hgh : 2740*gh≤2*T)
    (hnb : nb<2^(2*N)) (hnn : rows Q T<2^(2*N)) (hpos : 0<nb)
    (hbank : bank+nb≤addr free C 54) (hfbv : fbv+nb≤addr free C 54)
    (hgbv : gbv+nb≤addr free C 54) (hH : bankValues+(N+1)*nb≤addr free C 54)
    (hend : finish free C≤lim.space) (hw : (lim.space : ℤ)≤lim.word)
    (hword : (word N nb groups count R A : ℤ)≤lim.word)
    (hFhom : ∀ W, F W≠0 → rank W=fh) (hGhom : ∀ W, G W≠0 → rank W=gh)
    (hF : ∀ W, |F W|≤(A : ℤ)) (hG : ∀ W, |G W|≤(A : ℤ))
    (houtside : T<cacheCost Q)
    (hsorted : ∀ j k, j<k → k<nb → address (E.word j)<address (E.word k)) :
    LightWeightedPreparedState.Plan lim (addr free C 66) bankValues (addr free C 55)
      (config free C N A bank nb fbv T fh 58)
      (config free C N A bank nb gbv T gh 62) Q E F G := by sorry
