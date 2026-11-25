-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isSubobjectClosed_iInf
-- name    : PretorsionImageClosed.Statement.isSubobjectClosed_iInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:30:39.538936+00:00
-- url     : https://prove2.me/theorems/16ef9d6f-3829-540d-8cb4-e1ce9dd7bc2e
-- title:
--   Statement: is Subobject Closed i Inf
-- statement:
--   The Statement construction uses the is Subobject Closed i Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L206-L207
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L206-L207

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable {ι : Type*} (F : ι → Subcategory C)
variable {F} {T : Subcategory C} (hT : T.IsQuotientClosed) (h : ∀ i, IsPretorsionTheory T.prop (F i).prop)
include hT h
omit hT

theorem PretorsionImageClosed.Statement.isSubobjectClosed_iInf : (Subcategory.iInf F).IsSubobjectClosed := by sorry
