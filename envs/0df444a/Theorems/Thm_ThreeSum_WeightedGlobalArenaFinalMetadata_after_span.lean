-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalMetadata_after_span
-- name    : ThreeSum.WeightedGlobalArenaFinalMetadata.after_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:57:57.265533+00:00
-- url     : https://prove2.me/theorems/9b2adaad-0fbf-4518-aed2-a9ca2a7a1684
-- title:
--   Weighted Global Arena Final Metadata: after span
-- statement:
--   The real span construction writes only the eighth arena window.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L76-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L76-L95

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

theorem ThreeSum.WeightedGlobalArenaFinalMetadata.after_span {maps : Fin F→Weight m p} {τ : ℕ} {I : Input} {len : ℕ} {μ ν : ℕ→ℤ}
    (M : Metadata (r := r) maps τ I μ)
    (H : SameOutside μ ν (addr I.free I.capacity 8) len) (hlen : len≤I.capacity)
    (hprefix : I.prefixFree=addr I.free I.capacity 13) :
    Metadata (r := r) maps τ I ν := by sorry
