-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sInf_middle
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.sInf_middle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:41:49.056843+00:00
-- url     : https://prove2.me/theorems/ac751992-bc29-499a-9291-faa3036358e0
-- title:
--   Pretorsion Theory: s Inf middle
-- statement:
--   **Proposition 3.8**, meets: a nonempty meet of pretorsion theories with intersection `Z`
--   has intersection `Z`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L114-L135
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean#L114-L135

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.sInf_middle : (sInf S).middle = Z.prop := by sorry
