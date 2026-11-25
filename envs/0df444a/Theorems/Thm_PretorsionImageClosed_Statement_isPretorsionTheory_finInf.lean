-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_finInf
-- name    : PretorsionImageClosed.Statement.isPretorsionTheory_finInf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:41:11.382533+00:00
-- url     : https://prove2.me/theorems/08961a7e-edda-4d5b-9618-291801a71d0c
-- title:
--   Statement: is Pretorsion Theory fin Inf
-- statement:
--   The Statement construction uses the is Pretorsion Theory fin Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L180-L199
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L180-L199

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

theorem PretorsionImageClosed.Statement.isPretorsionTheory_finInf (J : Finset ι) : IsPretorsionTheory T.prop (finInf F J).prop := by sorry
