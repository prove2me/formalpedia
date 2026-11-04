-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedPreparedState_Plan_snapshot
-- name    : ThreeSum.LightWeightedPreparedState.Plan.snapshot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:44:53.09138+00:00
-- url     : https://prove2.me/theorems/6aace296-a284-4179-86e7-f8aa8d13eda7
-- title:
--   Plan: snapshot
-- statement:
--   The Plan construction uses the snapshot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedState.lean#L124-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedState.lean#L124-L133

import Definitions.Def_Submission_Weighted_PreparedWanted
import Definitions.Def_Submission_Weighted_PreparedState
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedPreparedState
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.LightWeightedPreparedWanted
set_option maxHeartbeats 6000000

theorem ThreeSum.LightWeightedPreparedState.Plan.snapshot {lim : Limits} {N out bankValues caps : ℕ} {f g : Config}
    {μ : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb} {F G : TritWord N→ℤ}
    (R : Plan lim out bankValues caps f g Q E F G)
    (hbank : ∀ j<f.nb, μ (f.bank+j)=(address (E.word j) : ℤ))
    (hF : ∀ j<f.nb, μ (f.bv+j)=binomialZeta F (E.word j))
    (hG : ∀ j<f.nb, μ (g.bv+j)=binomialZeta G (E.word j))
    (hH : LightWeightedBankSweep.Stages E
      (fun k => stageValue k (LightWeightedWantedQuery.H F G)) bankValues N μ) :
    Snapshot lim out bankValues caps f g μ Q E F G := by sorry
