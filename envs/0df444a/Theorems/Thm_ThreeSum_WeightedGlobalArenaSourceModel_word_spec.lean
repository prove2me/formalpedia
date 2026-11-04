-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceModel_word_spec
-- name    : ThreeSum.WeightedGlobalArenaSourceModel.word_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:10:20.186749+00:00
-- url     : https://prove2.me/theorems/5df016b5-c669-4b23-9e8f-2da1437a6312
-- title:
--   Weighted Global Arena Source Model: word spec
-- statement:
--   The Weighted Global Arena Source Model construction uses the word spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceModel.lean#L21-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceModel.lean#L21-L36

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceModel
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open TernaryCanonicalDictionaries WeightedGlobalNativeCompleteFrontend
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSourceModel.word_spec (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : Index (r := r) maps cap right) :
    (WeightedBankCanonical.enumeration (N m r) (cut m r)).word
      ((source (r := r) maps cap I right).key j.val)=
      WeightedGlobalCanonicalSourceBank.word right maps cap j := by sorry
