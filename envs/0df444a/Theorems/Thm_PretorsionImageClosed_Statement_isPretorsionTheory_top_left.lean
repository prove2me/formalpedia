-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_top_left
-- name    : PretorsionImageClosed.Statement.isPretorsionTheory_top_left
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:36:16.344831+00:00
-- url     : https://prove2.me/theorems/006943d7-b324-5f75-8d19-880377f99ebd
-- title:
--   Statement: is Pretorsion Theory top left
-- statement:
--   `(mod, F)` is a pretorsion theory for every subobject-closed `F`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L49-L56
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L49-L56

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

theorem PretorsionImageClosed.Statement.isPretorsionTheory_top_left {F : Subcategory C} (hF : F.IsSubobjectClosed) :
    IsPretorsionTheory (⊤ : Subcategory C).prop F.prop := by sorry
