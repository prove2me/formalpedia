-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_biproduct_fin
-- name    : PretorsionImageClosed.Statement.Subcategory.prop_biproduct_fin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:18:57.007808+00:00
-- url     : https://prove2.me/theorems/0cb5efb3-9d97-5064-9069-9b763f5ac970
-- title:
--   Subcategory: prop biproduct fin
-- statement:
--   The Subcategory construction uses the prop biproduct fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Biproducts.lean#L30-L37
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Biproducts.lean#L30-L37

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Biproducts_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Biproducts
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (Z : Subcategory C)

theorem PretorsionImageClosed.Statement.Subcategory.prop_biproduct_fin : ∀ {n : ℕ} (f : Fin n → C), (∀ j, Z.prop (f j)) → Z.prop (⨁ f)
  := by sorry
