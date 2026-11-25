-- Prove2me | Theorems.Thm_PretorsionImageClosed_Subobject_eq_of_isZero
-- name    : PretorsionImageClosed.Subobject.eq_of_isZero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:00:59.632131+00:00
-- url     : https://prove2.me/theorems/300b24c2-3474-4992-84db-de8b0fd3af68
-- title:
--   Subobject: eq of is Zero
-- statement:
--   A zero object has a unique subobject.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Quotients.lean#L69-L70
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Quotients.lean#L69-L70

module
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]

theorem PretorsionImageClosed.Subobject.eq_of_isZero {X : C} (hX : IsZero X) (S S' : Subobject X) : S = S' := by sorry
