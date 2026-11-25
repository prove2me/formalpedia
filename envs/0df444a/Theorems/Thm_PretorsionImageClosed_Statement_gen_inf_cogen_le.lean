-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_gen_inf_cogen_le
-- name    : PretorsionImageClosed.Statement.gen_inf_cogen_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:53:53.334839+00:00
-- url     : https://prove2.me/theorems/a52c36dd-3222-4c15-b674-519688b11081
-- title:
--   Statement: gen inf cogen le
-- statement:
--   **Corollary 4.9.** `Gen Z ∩ Cogen Z` is contained in every image-closed subcategory
--   containing `Z`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/LeastRealization.lean#L102-L106
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/LeastRealization.lean#L102-L106

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (Z : Subcategory C) (hZ : Z.IsImageClosed)
variable {Z}
variable (Z)

theorem PretorsionImageClosed.Statement.gen_inf_cogen_le {D : Subcategory C} (hD : D.IsImageClosed) (hZD : Z ≤ D) :
    Gen Z ⊓ Cogen Z ≤ D.prop := by sorry
