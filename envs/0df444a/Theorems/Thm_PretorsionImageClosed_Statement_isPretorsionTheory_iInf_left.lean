-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_iInf_left
-- name    : PretorsionImageClosed.Statement.isPretorsionTheory_iInf_left
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:44:18.482972+00:00
-- url     : https://prove2.me/theorems/d4482943-b7f1-4208-a06b-11b7b1479f6b
-- title:
--   Statement: is Pretorsion Theory i Inf left
-- statement:
--   **Proposition 3.5.** If `(T'', F'')` is a lower bound of a family `(Tᵢ, Fᵢ)` of pretorsion
--   theories, then `(⋂ Tᵢ, F'')` is a pretorsion theory.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L298-L328
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L298-L328

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

theorem PretorsionImageClosed.Statement.isPretorsionTheory_iInf_left {ι : Type*} {T F : ι → Subcategory C} {T'' F'' : Subcategory C}
    (h : ∀ i, IsPretorsionTheory (T i).prop (F i).prop) (h'' : IsPretorsionTheory T''.prop F''.prop)
    (hT : ∀ i, T'' ≤ T i) (hF : ∀ i, F i ≤ F'') :
    IsPretorsionTheory (Subcategory.iInf T).prop F''.prop := by sorry
