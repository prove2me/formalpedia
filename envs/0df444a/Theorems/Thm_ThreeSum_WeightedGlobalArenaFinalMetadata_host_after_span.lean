-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalMetadata_host_after_span
-- name    : ThreeSum.WeightedGlobalArenaFinalMetadata.host_after_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:03:56.521659+00:00
-- url     : https://prove2.me/theorems/747cf071-8ba9-4bee-a85d-68867f4b02e0
-- title:
--   Weighted Global Arena Final Metadata: host after span
-- statement:
--   The Weighted Global Arena Final Metadata construction uses the host after span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L97-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFinalMetadata.lean#L97-L105

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

theorem ThreeSum.WeightedGlobalArenaFinalMetadata.host_after_span {I : Input} {len : ℕ} {μ ν : ℕ→ℤ}
    (H : SameOutside μ ν (addr I.free I.capacity 8) len)
    (hcap : 106≤I.capacity) (args : List ℤ) (hlen : args.length=106)
    (hhost : Seg μ (addr I.free I.capacity 1) args) :
    Seg ν (addr I.free I.capacity 1) args := by sorry
