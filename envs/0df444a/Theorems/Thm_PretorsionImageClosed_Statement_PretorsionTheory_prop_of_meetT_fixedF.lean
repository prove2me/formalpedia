-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_prop_of_meetT_fixedF
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.prop_of_meetT_fixedF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:41:22.687806+00:00
-- url     : https://prove2.me/theorems/8f49352c-dc87-43c3-bcc7-e411152cc80f
-- title:
--   Pretorsion Theory: prop of meet T fixed F
-- statement:
--   An object of `⋂ Tᵢ ∩ F_Z` lies in `Z`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L76-L80
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L76-L80

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
open PretorsionImageClosed.Statement.PretorsionTheory
variable (S : Set (PretorsionTheory C)) (Z : Subcategory C)
variable {S Z} {P₀ : PretorsionTheory C} (hP₀ : P₀ ∈ S) (hS : ∀ P ∈ S, P.middle = Z.prop)
include hP₀ hS
omit hP₀ hS

theorem PretorsionImageClosed.Statement.PretorsionTheory.prop_of_meetT_fixedF {X : C} (hX : (meetT S).prop X) (hF : (fixedF S Z).prop X) :
    Z.prop X := by sorry
