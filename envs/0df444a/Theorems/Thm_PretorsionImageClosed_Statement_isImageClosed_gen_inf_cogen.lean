-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isImageClosed_gen_inf_cogen
-- name    : PretorsionImageClosed.Statement.isImageClosed_gen_inf_cogen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:53:24.154365+00:00
-- url     : https://prove2.me/theorems/4e277d29-ad4a-58fc-b873-b645dd8d5c62
-- title:
--   Statement: is Image Closed gen inf cogen
-- statement:
--   The Statement construction uses the is Image Closed gen inf cogen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/LeastRealization.lean#L94-L96
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/LeastRealization.lean#L94-L96

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

theorem PretorsionImageClosed.Statement.isImageClosed_gen_inf_cogen : IsImageClosed (Gen Z ⊓ Cogen Z) := by sorry
