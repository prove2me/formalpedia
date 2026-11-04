-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPostABI_selected_argv
-- name    : ThreeSum.WeightedGlobalColoredPostABI.selected_argv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:10:32.103094+00:00
-- url     : https://prove2.me/theorems/4c7ea670-0692-4a7a-80c0-10f047106f6e
-- title:
--   Weighted Global Colored Post ABI: selected argv
-- statement:
--   The Weighted Global Colored Post ABI construction uses the selected argv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L105-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L105-L114

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000

theorem ThreeSum.WeightedGlobalColoredPostABI.selected_argv {p m F r J : ℕ} [Fact p.Prime]
    (maps : Fin F→WeightedGlobalCoverGoodMaps.Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : WeightedGlobalArenaSourceSetup.Input)
    (U radix nA : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) :
    (LightWeightedGlobalCompactReporter.zeroCounts (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q
      (WeightedGlobalArenaPostSelection.selectedInput I U radix nA H A B C keysB keysC))).argv=
    (LightWeightedGlobalCompactReporter.zeroCounts (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap Q
      (WeightedGlobalArenaNativeComplete.input I U radix nA H A B C))).argv := by sorry
