-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_le_kernelSubobject
-- name    : PretorsionImageClosed.Statement.Subcategory.reject_le_kernelSubobject
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:27:14.58633+00:00
-- url     : https://prove2.me/theorems/36c9ff6f-2a2f-47c3-a67f-f27de88ed0b3
-- title:
--   Subcategory: reject le kernel Subobject
-- statement:
--   The reject is contained in the kernel of every morphism to an object of `F`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L284-L286
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L284-L286

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [Abelian C]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (T : Subcategory C) (X : C)
variable (F : Subcategory C)
variable [HasLength C]
variable {T X}
variable (X)
variable {F X}

theorem PretorsionImageClosed.Statement.Subcategory.reject_le_kernelSubobject (hF : F.IsSubobjectClosed) {Y : C} (g : X ⟶ Y) (hY : F.prop Y) :
    F.reject X ≤ kernelSubobject g := by sorry
