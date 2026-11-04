-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSetup_setup_left_input
-- name    : ThreeSum.WeightedGlobalArenaSourceSetup.setup_left_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:50:56.76059+00:00
-- url     : https://prove2.me/theorems/8e12e683-7c41-49d7-b125-a2bef6041747
-- title:
--   Weighted Global Arena Source Setup: setup left input
-- statement:
--   The Weighted Global Arena Source Setup construction uses the setup left input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceSetup.lean#L128-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceSetup.lean#L128-L130

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

theorem ThreeSum.WeightedGlobalArenaSourceSetup.setup_left_input (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) :
    (setup (r := r) maps τ cap Q I).left.input=I.leftInput := by sorry

attribute [defeq] ThreeSum.WeightedGlobalArenaSourceSetup.setup_left_input
