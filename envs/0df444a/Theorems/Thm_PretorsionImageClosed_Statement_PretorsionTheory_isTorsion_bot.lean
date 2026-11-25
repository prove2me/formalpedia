-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_isTorsion_bot
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.isTorsion_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:52:40.851013+00:00
-- url     : https://prove2.me/theorems/cb342a9b-1644-5189-9ec9-d7f916d5073d
-- title:
--   Pretorsion Theory: is Torsion bot
-- statement:
--   **Corollary 3.9**: `(0, mod)` is a torsion pair.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L123-L127
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L123-L127

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TorsionPairs
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory ZeroObject
variable {C : Type*} [Category C] [Abelian C]
variable [HasLength C]
open PretorsionImageClosed.Statement.PretorsionTheory

theorem PretorsionImageClosed.Statement.PretorsionTheory.isTorsion_bot : (⊥ : PretorsionTheory C).IsTorsion := by sorry
