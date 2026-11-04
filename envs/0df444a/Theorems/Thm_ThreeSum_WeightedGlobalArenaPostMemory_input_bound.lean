-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPostMemory_input_bound
-- name    : ThreeSum.WeightedGlobalArenaPostMemory.input_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:45:17.487506+00:00
-- url     : https://prove2.me/theorems/a91c8b82-d781-4c1d-a802-318b324f0156
-- title:
--   Weighted Global Arena Post Memory: input bound
-- statement:
--   The Weighted Global Arena Post Memory construction uses the input bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostMemory.lean#L69-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostMemory.lean#L69-L75

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCleanupLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostMemory
import Theorems.Thm_ThreeSum_WeightedGlobalMomentDetectorResources_input_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPostMemory
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 4000000
variable {p m F r J : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaPostMemory.input_bound (v : Fin r→ZMod p) :
    |(coefficientCode v : ℤ)|≤(p*(p+1)^r : ℕ) := by sorry
