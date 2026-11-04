-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSetup_setup_right_input
-- name    : ThreeSum.WeightedGlobalArenaSourceSetup.setup_right_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:58:48.574363+00:00
-- url     : https://prove2.me/theorems/2d444557-770a-4711-878b-60b772a9aa58
-- title:
--   Weighted Global Arena Source Setup: setup right input
-- statement:
--   The Weighted Global Arena Source Setup construction uses the setup right input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceSetup.lean#L131-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceSetup.lean#L131-L133

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCompleteFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontendResources
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceSetup
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaLayout
open TernaryCanonicalDictionaries LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceSetup.setup_right_input (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) :
    (setup (r := r) maps τ cap Q I).right.input=I.rightInput := by sorry

attribute [defeq] ThreeSum.WeightedGlobalArenaSourceSetup.setup_right_input
