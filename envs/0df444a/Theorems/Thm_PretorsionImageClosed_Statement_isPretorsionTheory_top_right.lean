-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_top_right
-- name    : PretorsionImageClosed.Statement.isPretorsionTheory_top_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:30:40.015464+00:00
-- url     : https://prove2.me/theorems/b6478b83-02c9-4398-93ff-1a5d20bdb262
-- title:
--   Statement: is Pretorsion Theory top right
-- statement:
--   `(T, mod)` is a pretorsion theory for every quotient-closed `T`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L40-L46
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L40-L46

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

theorem PretorsionImageClosed.Statement.isPretorsionTheory_top_right {T : Subcategory C} (hT : T.IsQuotientClosed) :
    IsPretorsionTheory T.prop (⊤ : Subcategory C).prop := by sorry
