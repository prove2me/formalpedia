-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceModel_original_rows
-- name    : ThreeSum.WeightedGlobalArenaSourceModel.original_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:10:54.605834+00:00
-- url     : https://prove2.me/theorems/84b03e8c-3067-4eed-8e58-411b978d378a
-- title:
--   Weighted Global Arena Source Model: original rows
-- statement:
--   The Weighted Global Arena Source Model construction uses the original rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceModel.lean#L69-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceModel.lean#L69-L82

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

theorem ThreeSum.WeightedGlobalArenaSourceModel.original_rows (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (original : ℕ→Fin r→ZMod p)
    (hin : ∀ i<(source (r := r) maps cap I right).NL,
      (source (r := r) maps cap I right).input i=(TernaryExtensionEncoding.coefficientCode (original i) : ℤ))
    (x : ℕ×ℕ) (hx : x∈(source (r := r) maps cap I right).records) :
    ∃ j : Index (r := r) maps cap right, j.val=x.2 ∧
      original x.1=WeightedGlobalCanonicalSourceBank.nativeRow right maps cap j := by sorry
