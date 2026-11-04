-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalMetadata_after_commit
-- name    : ThreeSum.WeightedGlobalArenaFinalMetadata.after_commit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:01:13.242534+00:00
-- url     : https://prove2.me/theorems/ce20a8cf-d3df-4f1e-8b56-93531c3102de
-- title:
--   Weighted Global Arena Final Metadata: after commit
-- statement:
--   The Weighted Global Arena Final Metadata construction uses the after commit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L107-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L107-L134

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedScoreReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostMemory
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFull
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalMetadata
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFinalMetadata
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory WeightedGlobalArenaPostMemory
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaFinalMetadata.after_commit {maps : Fin F→Weight m p} {τ : ℕ} {I : Input} {A : Inputs}
    {rows newSpan : ℕ} {μ ν : ℕ→ℤ}
    (M : Metadata (r := r) maps τ I μ)
    (H : LightWeightedGlobalPrefixFinish.Committed (config p r I A 0) rows newSpan μ ν)
    (hO : I.requesterCount≤I.capacity) (hspan : rows*A.J≤I.capacity)
    (hprefix : I.prefixFree=addr I.free I.capacity 13) :
    Metadata (r := r) maps τ I ν := by sorry
