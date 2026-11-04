-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedPreparedState_Snapshot_result_bound
-- name    : ThreeSum.LightWeightedPreparedState.Snapshot.result_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:47:36.012219+00:00
-- url     : https://prove2.me/theorems/965127e7-f4d4-4273-8bd4-7ccd9ecfd189
-- title:
--   Snapshot: result bound
-- statement:
--   The Snapshot construction uses the result bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedState.lean#L82-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedState.lean#L82-L92

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

theorem ThreeSum.LightWeightedPreparedState.Snapshot.result_bound {lim : Limits} {N out bankValues caps : ℕ}
    {f g : Config} {μ : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb}
    {F G : TritWord N→ℤ} (S : Snapshot lim out bankValues caps f g μ Q E F G) :
    |stageValue N (LightWeightedWantedQuery.H F G) Q|≤lim.word := by sorry
