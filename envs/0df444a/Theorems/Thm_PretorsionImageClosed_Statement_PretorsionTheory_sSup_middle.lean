-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sSup_middle
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.sSup_middle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:48:27.500039+00:00
-- url     : https://prove2.me/theorems/c45656b1-8182-4ee2-afa9-b06828694c01
-- title:
--   Pretorsion Theory: s Sup middle
-- statement:
--   **Proposition 3.8**, joins.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L150-L158
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L150-L158

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.sSup_middle : (sSup S).middle = Z.prop := by sorry
