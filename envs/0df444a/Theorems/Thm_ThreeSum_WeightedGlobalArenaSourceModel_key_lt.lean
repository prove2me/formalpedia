-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceModel_key_lt
-- name    : ThreeSum.WeightedGlobalArenaSourceModel.key_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:05:33.383912+00:00
-- url     : https://prove2.me/theorems/f9f5d36a-cce4-4761-b243-3b158ee0cc6a
-- title:
--   Weighted Global Arena Source Model: key lt
-- statement:
--   The Weighted Global Arena Source Model construction uses the key lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceModel.lean#L47-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceModel.lean#L47-L50

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
import Theorems.Thm_ThreeSum_LightSourceResidues_key_lt
import Theorems.Thm_ThreeSum_LightTernaryAppendKeys_key_lt

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceModel
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open TernaryCanonicalDictionaries WeightedGlobalNativeCompleteFrontend
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceModel.key_lt (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : Index (r := r) maps cap right) :
    (source (r := r) maps cap I right).key j.val<(source (r := r) maps cap I right).bank := by sorry
