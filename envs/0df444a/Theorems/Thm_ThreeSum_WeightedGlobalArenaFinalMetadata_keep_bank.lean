-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalMetadata_keep_bank
-- name    : ThreeSum.WeightedGlobalArenaFinalMetadata.keep_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:02:40.586194+00:00
-- url     : https://prove2.me/theorems/75cb313f-5f5b-41f2-b448-6f4c0a2fcb5b
-- title:
--   Weighted Global Arena Final Metadata: keep bank
-- statement:
--   The Weighted Global Arena Final Metadata construction uses the keep bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L23-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L23-L38

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

theorem ThreeSum.WeightedGlobalArenaFinalMetadata.keep_bank {I : Input} {A : Inputs} {seed K : ℕ}
    {D : Candidate (config p r I A seed)} {μ ν : ℕ→ℤ}
    (H : D.Done K μ ν) (hs : seed<I.capacity) (hcap : 106≤I.capacity)
    {x : ℕ} (hlo : addr I.free I.capacity 13≤x) (hhi : x<addr I.free I.capacity 16) :
    ν x=μ x := by sorry
