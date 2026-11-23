-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermDiag_toLinearMap_____eq_dotProduct_72a26b3ab9da
-- name    : P2M_GlobalTheory_HermDiag_toLinearMap_____eq_dotProduct_72a26b3ab9da
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:02.552457+00:00
-- url     : https://prove2.me/theorems/77b2d793-bc71-4cf2-8a34-5c4036cf68fb
-- title:
--   P2 M Global Theory Herm Diag to Linear Map     eq dot Product 72a26b3ab9da: P2 M Global Theory Herm Diag to Linear Map     eq dot Product 72a26b3ab9da
-- statement:
--   The P2 M Global Theory Herm Diag to Linear Map     eq dot Product 72a26b3ab9da construction uses the P2 M Global Theory Herm Diag to Linear Map     eq dot Product 72a26b3ab9da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L152-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L152-L157

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermDiag
open Module Matrix
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n]
variable [DecidableEq n]

theorem P2M_GlobalTheory_HermDiag_toLinearMap_____eq_dotProduct_72a26b3ab9da (c : E →+* E) (G : Matrix n n E) (x y : n → E) :
    Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G x y = x ⬝ᵥ G *ᵥ (c ∘ y) := by sorry

alias «GlobalTheory».«HermDiag».«toLinearMapₛₗ₂'_eq_dotProduct» := P2M_GlobalTheory_HermDiag_toLinearMap_____eq_dotProduct_72a26b3ab9da
