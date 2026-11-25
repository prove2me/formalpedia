-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_biproduct
-- name    : PretorsionImageClosed.Statement.Subcategory.prop_biproduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:51:45.346457+00:00
-- url     : https://prove2.me/theorems/2c62407d-1afa-4b1b-8d95-486ebddda3a1
-- title:
--   Subcategory: prop biproduct
-- statement:
--   A subcategory is closed under finite biproducts.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Biproducts.lean#L40-L45
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Biproducts.lean#L40-L45

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

theorem PretorsionImageClosed.Statement.Subcategory.prop_biproduct {J : Type*} [Fintype J] (f : J → C) (h : ∀ j, Z.prop (f j)) :
    Z.prop (⨁ f) := by sorry
