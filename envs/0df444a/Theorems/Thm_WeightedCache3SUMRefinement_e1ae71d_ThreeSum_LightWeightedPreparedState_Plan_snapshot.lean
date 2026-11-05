-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPreparedState_Plan_snapshot
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedState.Plan.snapshot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:01:05.767835+00:00
-- url     : https://prove2.me/theorems/16f2a9fb-ed3f-4828-8383-88959dcb5eac
-- title:
--   snapshot
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PreparedState.lean#L124-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PreparedState.lean#L124-L133

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedWanted
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedState
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedState
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.LightWeightedPreparedWanted
set_option maxHeartbeats 6000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedState.Plan.snapshot {lim : Limits} {N out bankValues caps : ℕ} {f g : Config}
    {μ : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb} {F G : TritWord N→ℤ}
    (R : Plan lim out bankValues caps f g Q E F G)
    (hbank : ∀ j<f.nb, μ (f.bank+j)=(address (E.word j) : ℤ))
    (hF : ∀ j<f.nb, μ (f.bv+j)=binomialZeta F (E.word j))
    (hG : ∀ j<f.nb, μ (g.bv+j)=binomialZeta G (E.word j))
    (hH : LightWeightedBankSweep.Stages E
      (fun k => stageValue k (LightWeightedWantedQuery.H F G)) bankValues N μ) :
    Snapshot lim out bankValues caps f g μ Q E F G := by sorry
