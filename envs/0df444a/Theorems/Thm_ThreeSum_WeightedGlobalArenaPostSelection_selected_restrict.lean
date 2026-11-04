-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPostSelection_selected_restrict
-- name    : ThreeSum.WeightedGlobalArenaPostSelection.selected_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:35:38.306538+00:00
-- url     : https://prove2.me/theorems/61210fff-f9f2-4b26-816a-de062e5134bf
-- title:
--   Weighted Global Arena Post Selection: selected restrict
-- statement:
--   The Weighted Global Arena Post Selection construction uses the selected restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostSelection.lean#L35-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPostSelection.lean#L35-L43

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

theorem ThreeSum.WeightedGlobalArenaPostSelection.selected_restrict (I : Input) (U radix nA : ℕ)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) :
    selectedInput I U radix nA H A B C keysB keysC =
      WeightedGlobalArenaPairRestriction.restrict
        (WeightedGlobalArenaNativeComplete.input I U radix nA H A B C)
        (indices keysB I.nB).length (indices keysC I.nC).length
        (index keysB I.nB) (index keysC I.nC) := by sorry
