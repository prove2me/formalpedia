-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isSubobjectClosed_finInf
-- name    : PretorsionImageClosed.Statement.isSubobjectClosed_finInf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:41:32.465458+00:00
-- url     : https://prove2.me/theorems/bf323ad3-2906-455d-bb9b-3d959114dda6
-- title:
--   Statement: is Subobject Closed fin Inf
-- statement:
--   The Statement construction uses the is Subobject Closed fin Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L202-L203
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L202-L203

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
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

theorem PretorsionImageClosed.Statement.isSubobjectClosed_finInf (J : Finset ι) : (finInf F J).IsSubobjectClosed := by sorry
