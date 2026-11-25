-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_isTorsion_top
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.isTorsion_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:52:57.934955+00:00
-- url     : https://prove2.me/theorems/dffeb534-68b4-4d7a-b6e7-e34197bde844
-- title:
--   Pretorsion Theory: is Torsion top
-- statement:
--   **Corollary 3.9**: `(mod, 0)` is a torsion pair.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L130-L134
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L130-L134

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.isTorsion_top : (⊤ : PretorsionTheory C).IsTorsion := by sorry
