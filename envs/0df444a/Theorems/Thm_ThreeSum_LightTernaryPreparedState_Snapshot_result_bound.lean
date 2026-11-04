-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPreparedState_Snapshot_result_bound
-- name    : ThreeSum.LightTernaryPreparedState.Snapshot.result_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:44:53.892077+00:00
-- url     : https://prove2.me/theorems/c131a92d-9ed6-4070-b8e9-941bc7b6ac77
-- title:
--   Snapshot: result bound
-- statement:
--   The Snapshot construction uses the result bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPreparedState.lean#L76-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPreparedState.lean#L76-L86

import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedWanted
import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedState
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPreparedState
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryBankStageModel ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryQueryPlan
open ThreeSum.LightTernaryPreparedWanted
set_option maxHeartbeats 6000000

theorem ThreeSum.LightTernaryPreparedState.Snapshot.result_bound {lim : Limits} {N out bankValues caps : ℕ}
    {f g : Config} {μ : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb}
    {F G : TritWord N→ℤ} (S : Snapshot lim out bankValues caps f g μ Q E F G) :
    |stageValue N (LightTernaryWantedQuery.H F G) Q|≤lim.word := by sorry
