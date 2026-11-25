-- Prove2me | Theorems.Thm_PretorsionImageClosed_Subobject_exists_minimal_of_nonempty
-- name    : PretorsionImageClosed.Subobject.exists_minimal_of_nonempty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:12:25.623877+00:00
-- url     : https://prove2.me/theorems/97f70d85-2c9e-4117-bdab-68af78274bc4
-- title:
--   Subobject: exists minimal of nonempty
-- statement:
--   Every nonempty set of subobjects contains a minimal element.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L123-L130
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L123-L130

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Definitions.Def_PretorsionImageClosed_Length_Basic
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasLength C]
variable {X : C} (S : Subobject X)

theorem PretorsionImageClosed.Subobject.exists_minimal_of_nonempty (s : Set (Subobject X)) (hs : s.Nonempty) :
    ∃ S ∈ s, ∀ T ∈ s, T ≤ S → T = S := by sorry
