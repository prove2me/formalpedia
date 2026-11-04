-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontendResources_plan
-- name    : ThreeSum.WeightedGlobalArenaFrontendResources.plan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:32:04.712144+00:00
-- url     : https://prove2.me/theorems/fd35ce31-04f2-4215-8095-be801a872048
-- title:
--   Weighted Global Arena Frontend Resources: plan
-- statement:
--   The Weighted Global Arena Frontend Resources construction uses the plan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFrontendResources.lean#L107-L163
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFrontendResources.lean#L107-L163

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontendResources
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_plan
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFrontendResources
open Light WeightedGlobalArenaLayout TernaryJointType WeightedGlobalBank TernaryEuler
open WeightedGlobalFrontendResources LightWeightedNearPair LightWeightedQueryPlan
open LightWeightedPreparedWanted WeightedBankStageModel TernaryCodeSemantics
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaFrontendResources.plan {lim : Limits} {free C N R A bank nb fbv gbv T fh gh bankValues groups count : ℕ}
    (Q : TritWord N) (E : Enumeration N T nb) (F G : TritWord N→ℤ)
    (hrows : rows Q T≤R) (hR : R≤C) (hN : N≤C) (hpowers : 2*N+1≤C)
    (hmetadata : 2*N*R+N≤C) (hdivision : eulerBound N A+3≤C)
    (hCut : T≤1025*N) (hfDegree : fh≤2*N) (hgDegree : gh≤2*N) (hfh : 1025*fh≤2*T) (hgh : 1025*gh≤2*T)
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
