-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_plan
-- name    : ThreeSum.WeightedGlobalFrontendResources.plan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:32:50.965042+00:00
-- url     : https://prove2.me/theorems/fda2fa1e-fdf0-4787-94b5-dad2d43712d0
-- title:
--   Weighted Global Frontend Resources: plan
-- statement:
--   A complete scalar plan for the actual prepared query, instantiated from
--   one canonical layout and elementary bounds on the source histograms.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L179-L238
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/FrontendResources.lean#L179-L238

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

theorem ThreeSum.WeightedGlobalFrontendResources.plan {lim : Limits} {a N R A bank nb fbv gbv T fh gh bankValues groups count : ℕ}
    (Q : TritWord N) (E : Enumeration N T nb) (F G : TritWord N→ ℤ)
    (hrows : rows Q T≤ R) (hCut : T≤1025*N) (hfDegree : fh≤2*N) (hgDegree : gh≤2*N)
    (hfh : 1025*fh≤2*T) (hgh : 1025*gh≤2*T)
    (hnb : nb< 2^(2*N)) (hnn : rows Q T< 2^(2*N)) (hpos : 0< nb)
    (hbank : bank+nb≤ a) (hfbv : fbv+nb≤ a) (hgbv : gbv+nb≤ a)
    (hH : bankValues+(N+1)*nb≤ a)
    (hend : heapEnd a N R A≤ lim.space) (hw : (lim.space:ℤ)≤ lim.word)
    (hword : (word N nb groups count R A:ℤ)≤ lim.word)
    (hFhom : ∀ W, F W≠ 0→ rank W=fh) (hGhom : ∀ W, G W≠ 0→ rank W=gh)
    (hF : ∀ W, |F W|≤ (A:ℤ)) (hG : ∀ W, |G W|≤ (A:ℤ))
    (houtside : T< WeightedBankEnumeration.cacheCost Q)
    (hsorted : ∀ j k, j< k→ k< nb→ address (E.word j)< address (E.word k)) :
    LightWeightedPreparedState.Plan lim (out a N R A) bankValues (caps a R)
      (config a N R A bank nb fbv T fh (fws a N R))
      (config a N R A bank nb gbv T gh (gws a N R A)) Q E F G := by sorry
