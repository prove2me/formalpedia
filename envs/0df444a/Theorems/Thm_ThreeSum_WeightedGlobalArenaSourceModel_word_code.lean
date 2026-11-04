-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceModel_word_code
-- name    : ThreeSum.WeightedGlobalArenaSourceModel.word_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:17:25.948014+00:00
-- url     : https://prove2.me/theorems/d17c2f5d-6468-42ef-81f9-a8dc9348106c
-- title:
--   Weighted Global Arena Source Model: word code
-- statement:
--   The Weighted Global Arena Source Model construction uses the word code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceModel.lean#L52-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceModel.lean#L52-L67

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

theorem ThreeSum.WeightedGlobalArenaSourceModel.word_code (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : Index (r := r) maps cap right) :
    LightTernarySourceHost.dictionary (source (r := r) maps cap I right).ys
      (source (r := r) maps cap I right).p1 r j.val=
      ((source (r := r) maps cap I right).codes ((source (r := r) maps cap I right).key j.val) : ℤ) := by sorry
