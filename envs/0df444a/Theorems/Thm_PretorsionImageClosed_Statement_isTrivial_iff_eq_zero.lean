-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isTrivial_iff_eq_zero
-- name    : PretorsionImageClosed.Statement.isTrivial_iff_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:48:38.4278+00:00
-- url     : https://prove2.me/theorems/266b3b65-939b-470d-acde-c58e92827346
-- title:
--   Statement: is Trivial iff eq zero
-- statement:
--   With `Z` consisting of zero objects, the `Z`-trivial morphisms are the zero morphisms.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L42-L48
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean#L42-L48

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

theorem PretorsionImageClosed.Statement.isTrivial_iff_eq_zero {Z : Subcategory C} (hZ : ∀ X, Z.prop X → IsZero X) {X Y : C}
    (f : X ⟶ Y) : IsTrivial Z.prop f ↔ f = 0 := by sorry
