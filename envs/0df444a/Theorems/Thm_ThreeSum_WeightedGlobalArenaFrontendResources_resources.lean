-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontendResources_resources
-- name    : ThreeSum.WeightedGlobalArenaFrontendResources.resources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:19:59.588955+00:00
-- url     : https://prove2.me/theorems/905138ed-b875-4817-89d9-ab20f6f15234
-- title:
--   Weighted Global Arena Frontend Resources: resources
-- statement:
--   The Weighted Global Arena Frontend Resources construction uses the resources property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFrontendResources.lean#L39-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFrontendResources.lean#L39-L105

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontendResources
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_resources
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFrontendResources
open Light WeightedGlobalArenaLayout TernaryJointType WeightedGlobalBank TernaryEuler
open WeightedGlobalFrontendResources LightWeightedNearPair LightWeightedQueryPlan
open LightWeightedPreparedWanted WeightedBankStageModel TernaryCodeSemantics
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaFrontendResources.resources {lim : Limits} {free C N R A bank nb bv T h wsSlot rows groups count : ℕ}
    (hws : wsSlot=58 ∨ wsSlot=62)
    (hrows : rows≤R) (hR : R≤C) (hN : N≤C) (hpowers : 2*N+1≤C)
    (hmetadata : 2*N*R+N≤C) (hdivision : eulerBound N A+3≤C)
    (hCut : T≤1025*N) (hT : h≤2*N) (hh : 1025*h≤2*T) (hnb : nb<2^(2*N)) (hnn : rows<2^(2*N)) (hpos : 0<nb)
    (hbank : bank+nb≤addr free C 54) (hbv : bv+nb≤addr free C 54)
    (hend : finish free C≤lim.space) (hw : (lim.space : ℤ)≤lim.word)
    (hword : (word N nb groups count R A : ℤ)≤lim.word)
    (F : TritWord N→ℤ) (hhom : ∀ W, F W≠0 → rank W=h)
    (hF : ∀ W, |F W|≤(A : ℤ)) :
    Resources lim rows (config free C N A bank nb bv T h wsSlot) F := by sorry
