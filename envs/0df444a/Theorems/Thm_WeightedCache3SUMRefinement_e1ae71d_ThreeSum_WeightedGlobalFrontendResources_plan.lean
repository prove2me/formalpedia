-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFrontendResources_plan
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFrontendResources.plan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:25:28.545339+00:00
-- url     : https://prove2.me/theorems/904ae0cd-c72e-41c5-96a4-e4411ed3f862
-- title:
--   plan
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/FrontendResources.lean#L179-L238
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/FrontendResources.lean#L179-L238

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_FrontendResources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.WeightedGlobalBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFrontendResources.plan {lim : Limits} {a N R A bank nb fbv gbv T fh gh bankValues groups count : ℕ}
    (Q : TritWord N) (E : Enumeration N T nb) (F G : TritWord N→ ℤ)
    (hrows : rows Q T≤ R) (hCut : T≤2740*N) (hfDegree : fh≤2*N) (hgDegree : gh≤2*N)
    (hfh : 2740*fh≤2*T) (hgh : 2740*gh≤2*T)
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
