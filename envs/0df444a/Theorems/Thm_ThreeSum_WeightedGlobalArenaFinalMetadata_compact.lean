-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalMetadata_compact
-- name    : ThreeSum.WeightedGlobalArenaFinalMetadata.compact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:08:42.668002+00:00
-- url     : https://prove2.me/theorems/f5ce81ce-959c-4ffc-8863-0d2e8e6ff447
-- title:
--   Weighted Global Arena Final Metadata: compact
-- statement:
--   The Weighted Global Arena Final Metadata construction uses the compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L70-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L70-L73

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedScoreReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostMemory
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFull
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalMetadata
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFinalMetadata
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory WeightedGlobalArenaPostMemory
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaFinalMetadata.compact {maps : Fin F→Weight m p} {τ : ℕ} {I : Input} {μ : ℕ→ℤ}
    (M : Metadata (r := r) maps τ I μ) (nB nC : ℕ) (fB fC : ℕ→ℕ) :
    Metadata (r := r) maps τ (WeightedGlobalArenaPairRestriction.restrict I nB nC fB fC) μ := by sorry
