-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_inf
-- name    : PretorsionImageClosed.Statement.isPretorsionTheory_inf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:38:58.170026+00:00
-- url     : https://prove2.me/theorems/1ab4d67f-b479-4daf-82be-45df35730bc1
-- title:
--   Statement: is Pretorsion Theory inf
-- statement:
--   **Proposition 3.2**, binary case: if `(T, F₁)` and `(T, F₂)` are pretorsion theories, so is
--   `(T, F₁ ∩ F₂)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L126-L145
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L126-L145

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

theorem PretorsionImageClosed.Statement.isPretorsionTheory_inf {T F₁ F₂ : Subcategory C} (h₁ : IsPretorsionTheory T.prop F₁.prop)
    (h₂ : IsPretorsionTheory T.prop F₂.prop) : IsPretorsionTheory T.prop (F₁ ⊓ F₂).prop := by sorry
