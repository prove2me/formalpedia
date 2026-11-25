-- Prove2me | Theorems.Thm_PretorsionImageClosed_Subobject_exists_maximal_of_nonempty
-- name    : PretorsionImageClosed.Subobject.exists_maximal_of_nonempty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:12:27.339488+00:00
-- url     : https://prove2.me/theorems/d482d4f7-b6c9-4574-a1b1-9f908a8ce36e
-- title:
--   Subobject: exists maximal of nonempty
-- statement:
--   Every nonempty set of subobjects contains a maximal element: one that is
--   not strictly below any other member.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L111-L120
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean#L111-L120

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

theorem PretorsionImageClosed.Subobject.exists_maximal_of_nonempty (s : Set (Subobject X)) (hs : s.Nonempty) :
    ∃ S ∈ s, ∀ T ∈ s, S ≤ T → S = T := by sorry
