-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_prop_of_mono_of_meetT
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.prop_of_mono_of_meetT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:41:17.996902+00:00
-- url     : https://prove2.me/theorems/95de087c-dbd5-42dd-8996-8e86839bada2
-- title:
--   Pretorsion Theory: prop of mono of meet T
-- statement:
--   An object of `⋂ Tᵢ` embedding in an object of `Z` lies in `Z`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L50-L54
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L50-L54

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.prop_of_mono_of_meetT {M N : C} (i : M ⟶ N) [Mono i] (hM : (meetT S).prop M)
    (hN : Z.prop N) : Z.prop M := by sorry
