-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalExecutable_main_lookup
-- name    : ThreeSum.WeightedGlobalExecutable.main_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:53:01.387217+00:00
-- url     : https://prove2.me/theorems/3f9a9bb2-8505-4229-8ad9-d9f033dfab76
-- title:
--   Weighted Global Executable: main lookup
-- statement:
--   The Weighted Global Executable construction uses the main lookup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExecutable.lean#L71-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExecutable.lean#L71-L78

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgram
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_Weighted_Global_TernaryExecutable
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_main
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_ThreeSum_LightWeightedGlobalFastProgram_main_lookup
attribute [local simp] ThreeSum.LightTernaryCountFrontend.main
attribute [local simp] ThreeSum.LightWeightedCountFrontend.main


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalExecutable
open Light WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCanonicalDictionaries
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalExecutable.main_lookup (maps : Fin F→Weight m p) (τ cap M radix K D E κ : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) :
    (program maps τ cap M radix K D E κ Q)[main (p := p) K]?=
      some (LightWeightedGlobalFastProgram.body
        (LightWeightedGlobalFastProgram.hostEntry (color maps τ cap M radix K D E Q))) := by sorry
