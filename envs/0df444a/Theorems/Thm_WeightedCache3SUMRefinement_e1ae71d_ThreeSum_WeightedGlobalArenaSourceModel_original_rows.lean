-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceModel_original_rows
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceModel.original_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:08:44.06797+00:00
-- url     : https://prove2.me/theorems/e7d5b219-3a8b-4b52-9e50-d510eecf1782
-- title:
--   original_rows
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceModel.lean#L69-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceModel.lean#L69-L82

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceModel
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceModel
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open TernaryCanonicalDictionaries WeightedGlobalNativeCompleteFrontend
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceModel.original_rows (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (original : ℕ→Fin r→ZMod p)
    (hin : ∀ i<(source (r := r) maps cap I right).NL,
      (source (r := r) maps cap I right).input i=(TernaryExtensionEncoding.coefficientCode (original i) : ℤ))
    (x : ℕ×ℕ) (hx : x∈(source (r := r) maps cap I right).records) :
    ∃ j : Index (r := r) maps cap right, j.val=x.2 ∧
      original x.1=WeightedGlobalCanonicalSourceBank.nativeRow right maps cap j := by sorry
