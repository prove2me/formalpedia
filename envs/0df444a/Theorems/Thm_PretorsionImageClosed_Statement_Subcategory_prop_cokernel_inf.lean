-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_inf
-- name    : PretorsionImageClosed.Statement.Subcategory.prop_cokernel_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:31:03.574399+00:00
-- url     : https://prove2.me/theorems/420f12c3-669f-5007-a014-96c198e018ad
-- title:
--   Subcategory: prop cokernel inf
-- statement:
--   `X/(K ⊓ K')` embeds into `X/K ⊞ X/K'`, so the quotients lying in a
--   subobject-closed subcategory are closed under intersection.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L93-L124
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L93-L124

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

theorem PretorsionImageClosed.Statement.Subcategory.prop_cokernel_inf (hF : F.IsSubobjectClosed) {K K' : Subobject X}
    (hK : F.prop (cokernel K.arrow)) (hK' : F.prop (cokernel K'.arrow)) :
    F.prop (cokernel (K ⊓ K').arrow) := by sorry
