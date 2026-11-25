-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_reject_iff
-- name    : PretorsionImageClosed.Statement.Subcategory.le_reject_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:26:54.340803+00:00
-- url     : https://prove2.me/theorems/729ffc16-d87e-4a71-bbdd-48905c2c3bee
-- title:
--   Subcategory: le reject iff
-- statement:
--   Definition 2.7: the reject is the intersection of the kernels of all
--   morphisms to objects of `F`, in the form: a subobject is contained in the
--   reject iff it is killed by every morphism to an object of `F`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L296-L305
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L296-L305

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

theorem PretorsionImageClosed.Statement.Subcategory.le_reject_iff (hF : F.IsSubobjectClosed) {K : Subobject X} :
    K ≤ F.reject X ↔ ∀ {Y : C} (g : X ⟶ Y), F.prop Y → K.arrow ≫ g = 0 := by sorry
