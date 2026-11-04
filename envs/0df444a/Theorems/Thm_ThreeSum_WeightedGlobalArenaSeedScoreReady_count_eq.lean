-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedScoreReady_count_eq
-- name    : ThreeSum.WeightedGlobalArenaSeedScoreReady.count_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:18:51.88596+00:00
-- url     : https://prove2.me/theorems/910edba8-5ba0-4a59-b8b9-9f097133dff1
-- title:
--   Weighted Global Arena Seed Score Ready: count eq
-- statement:
--   The Weighted Global Arena Seed Score Ready construction uses the count eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedScoreReady.lean#L60-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedScoreReady.lean#L60-L66

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedScoreReady
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSeedScoreReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaSeedScoreReady.count_eq (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (seed : ℕ)
    (D : Data (config p r I A seed)) :
    (setup (r := r) maps τ cap Q (sourceInput I A seed D)).front.count=
      D.H (4^fixedLength m) F (WeightedGlobalGoodOutputCatalog.raws maps τ)
        (WeightedGlobalGoodOutputCatalog.wordCodes maps τ) (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) := by sorry
