-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_iInf
-- name    : PretorsionImageClosed.Statement.isPretorsionTheory_iInf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:44:03.443955+00:00
-- url     : https://prove2.me/theorems/380ff8f3-db15-41b3-a523-2fabc7e8ae5b
-- title:
--   Statement: is Pretorsion Theory i Inf
-- statement:
--   **Proposition 3.2.** If `(T, Fᵢ)` is a pretorsion theory for every `i`, so is `(T, ⋂ Fᵢ)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L243-L250
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L243-L250

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

theorem PretorsionImageClosed.Statement.isPretorsionTheory_iInf : IsPretorsionTheory T.prop (Subcategory.iInf F).prop := by sorry
