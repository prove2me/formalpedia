-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_F_le_fixedF
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.F_le_fixedF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:40:52.979707+00:00
-- url     : https://prove2.me/theorems/ae746a62-716f-4c57-af2a-99423853807c
-- title:
--   Pretorsion Theory: F le fixed F
-- statement:
--   The Pretorsion Theory construction uses the F le fixed F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L65-L72
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L65-L72

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
omit hP₀

theorem PretorsionImageClosed.Statement.PretorsionTheory.F_le_fixedF {P : PretorsionTheory C} (hP : P ∈ S) : P.F ≤ fixedF S Z := by sorry
