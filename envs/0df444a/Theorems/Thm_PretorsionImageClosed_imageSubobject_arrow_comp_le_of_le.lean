-- Prove2me | Theorems.Thm_PretorsionImageClosed_imageSubobject_arrow_comp_le_of_le
-- name    : PretorsionImageClosed.imageSubobject_arrow_comp_le_of_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:42:00.572874+00:00
-- url     : https://prove2.me/theorems/bf2d69ed-440f-4260-a219-0c03c4664226
-- title:
--   Pretorsion Image Closed: image Subobject arrow comp le of le
-- statement:
--   The Pretorsion Image Closed construction uses the image Subobject arrow comp le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L54-L57
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L54-L57

module
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]

theorem PretorsionImageClosed.imageSubobject_arrow_comp_le_of_le {X Y : C} {S S' : Subobject X} (h : S ≤ S')
    (p : X ⟶ Y) : imageSubobject (S.arrow ≫ p) ≤ imageSubobject (S'.arrow ≫ p) := by sorry
