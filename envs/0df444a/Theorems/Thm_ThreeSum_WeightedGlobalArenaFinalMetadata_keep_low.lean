-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalMetadata_keep_low
-- name    : ThreeSum.WeightedGlobalArenaFinalMetadata.keep_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:04:40.615585+00:00
-- url     : https://prove2.me/theorems/2310a349-247d-449f-855b-2e838e8c3843
-- title:
--   Weighted Global Arena Final Metadata: keep low
-- statement:
--   The Weighted Global Arena Final Metadata construction uses the keep low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L136-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L136-L151

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedScoreReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostMemory
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFull
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalMetadata
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFinalMetadata
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory WeightedGlobalArenaPostMemory
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaFinalMetadata.keep_low {I : Input} {A : Inputs} {seed K : ℕ}
    {D : Candidate (config p r I A seed)} {μ ν : ℕ→ℤ}
    (H : D.Done K μ ν) {x : ℕ} (hx : x<addr I.free I.capacity 9)
    (hne : x≠addr I.free I.capacity 1+104) : ν x=μ x := by sorry
