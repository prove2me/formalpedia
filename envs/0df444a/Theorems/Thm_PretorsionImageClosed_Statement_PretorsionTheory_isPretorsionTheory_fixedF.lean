-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_isPretorsionTheory_fixedF
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.isPretorsionTheory_fixedF
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:48:13.25096+00:00
-- url     : https://prove2.me/theorems/bbce90f9-5f58-415a-8c7b-9fc89a9569c8
-- title:
--   Pretorsion Theory: is Pretorsion Theory fixed F
-- statement:
--   The Pretorsion Theory construction uses the is Pretorsion Theory fixed F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L82-L110
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L82-L110

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.isPretorsionTheory_fixedF : IsPretorsionTheory (meetT S).prop (fixedF S Z).prop := by sorry
