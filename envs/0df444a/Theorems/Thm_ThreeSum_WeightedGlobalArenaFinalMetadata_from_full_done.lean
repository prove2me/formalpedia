-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalMetadata_from_full_done
-- name    : ThreeSum.WeightedGlobalArenaFinalMetadata.from_full_done
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:02:39.121331+00:00
-- url     : https://prove2.me/theorems/ae897029-fd18-4fdc-9506-c1ce27d858f1
-- title:
--   Weighted Global Arena Final Metadata: from full done
-- statement:
--   The real replay output, together with preserved literal bank cells,
--   supplies all final metadata. No wanted-list representation is assumed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L42-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L42-L68

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

theorem ThreeSum.WeightedGlobalArenaFinalMetadata.from_full_done (maps : Fin F→Weight m p) (τ cap K : ℕ)
    (I : Input) (A : Inputs) (seed : ℕ) (D : Candidate (config p r I A seed))
    (μ ν : ℕ→ℤ)
    (H : D.FullDone K (4^fixedLength m) F (WeightedGlobalGoodOutputCatalog.raws maps τ)
      (WeightedGlobalGoodOutputCatalog.wordCodes maps τ) (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) μ ν)
    (hs : seed<I.capacity) (hcap : 106≤I.capacity)
    (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hbankEnd : I.prefixFree+nb m r≤addr I.free I.capacity 16)
    (hpowerEnd : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16)
    (hcodes : Seg μ I.prefixFree ((bankCodes m r).map (fun c=>(c : ℤ))))
    (hpowers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m r)) (2*N m r)) :
    Metadata (r := r) maps τ (sourceInput I A seed D.data) ν := by sorry
