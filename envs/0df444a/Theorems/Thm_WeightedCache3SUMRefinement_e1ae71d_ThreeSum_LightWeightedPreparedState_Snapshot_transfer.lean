-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPreparedState_Snapshot_transfer
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedState.Snapshot.transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:01:37.502304+00:00
-- url     : https://prove2.me/theorems/7e6ce5c8-eda4-457c-a685-16aa08593b68
-- title:
--   transfer
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PreparedState.lean#L66-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PreparedState.lean#L66-L80

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPreparedState.Snapshot.transfer {lim : Limits} {N out bankValues caps cut : ℕ}
    {f g : Config} {μ ν : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb}
    {F G : TritWord N→ℤ} (S : Snapshot lim out bankValues caps f g μ Q E F G)
    (H : ∀ x<cut, ν x=μ x)
    (hcodes : f.bank+f.nb≤cut) (hF : f.bv+f.nb≤cut) (hG : g.bv+f.nb≤cut)
    (hH : bankValues+(N+1)*f.nb≤cut) : Snapshot lim out bankValues caps f g ν Q E F G := by sorry
