-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalMetadata_host_from_full_done
-- name    : ThreeSum.WeightedGlobalArenaFinalMetadata.host_from_full_done
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:04:45.060195+00:00
-- url     : https://prove2.me/theorems/668648c0-8465-4874-b680-4eb323c256df
-- title:
--   Weighted Global Arena Final Metadata: host from full done
-- statement:
--   The replay's literal header104 store completes the106 live host words.
--   All other words are preserved by the actual candidate program.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L155-L174
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L155-L174

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

theorem ThreeSum.WeightedGlobalArenaFinalMetadata.host_from_full_done (maps : Fin F→Weight m p) (τ cap K : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (seed : ℕ)
    (D : Candidate (config p r I A seed)) (μ ν : ℕ→ℤ)
    (H : D.FullDone K (4^fixedLength m) F (WeightedGlobalGoodOutputCatalog.raws maps τ)
      (WeightedGlobalGoodOutputCatalog.wordCodes maps τ) (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) μ ν)
    (hcap : 106≤I.capacity)
    (hheader : ∀i<106,i≠104→μ (addr I.free I.capacity 1+i)=
      (setup (r := r) maps τ cap Q (sourceInput I A seed D.data)).argv.getD i 0) :
    Seg ν (addr I.free I.capacity 1)
      (setup (r := r) maps τ cap Q (sourceInput I A seed D.data)).argv := by sorry
