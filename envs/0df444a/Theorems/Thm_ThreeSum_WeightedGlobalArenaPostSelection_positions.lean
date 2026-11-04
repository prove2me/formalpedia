-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPostSelection_positions
-- name    : ThreeSum.WeightedGlobalArenaPostSelection.positions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:32:55.284921+00:00
-- url     : https://prove2.me/theorems/dd465255-ec54-4c3f-b035-e16fdec47bc1
-- title:
--   Weighted Global Arena Post Selection: positions
-- statement:
--   The Weighted Global Arena Post Selection construction uses the positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostSelection.lean#L106-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostSelection.lean#L106-L117

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCompactSupport
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaMomentResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCountSeed
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPostSelection
open Light LightOriginalSurvivors LightWeightedGlobalPostSelection
open WeightedGlobalArenaSourceSetup WeightedGlobalCoverGoodMaps TernarySignedReduction
open TernaryExtensionEncoding WeightedGlobalArenaLayout
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaPostSelection.positions (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (U radix nA : ℕ)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) :
    let I' := selectedInput I U radix nA H A B C keysB keysC
    ∀i<(setup (r := r) maps τ cap Q I').front.count,
      WeightedGlobalArenaNativeComplete.originalPosition (r := r) maps τ I' i<nA := by sorry
