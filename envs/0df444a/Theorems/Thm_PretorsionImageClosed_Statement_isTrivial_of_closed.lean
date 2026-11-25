-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isTrivial_of_closed
-- name    : PretorsionImageClosed.Statement.isTrivial_of_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:27:26.978012+00:00
-- url     : https://prove2.me/theorems/04cf46ec-d070-4b47-bb54-6b8a6256cfee
-- title:
--   Statement: is Trivial of closed
-- statement:
--   A morphism from an object of a quotient-closed `T` to an object of a subobject-closed `F`
--   factors through its image, which lies in `T ∩ F`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L134-L138
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L134-L138

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
open Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (T F : Subcategory C) (X : C)
variable {T F X}

theorem PretorsionImageClosed.Statement.isTrivial_of_closed (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed) {X Y : C}
    (f : X ⟶ Y) (hX : T.prop X) (hY : F.prop Y) : IsTrivial (T.prop ⊓ F.prop) f := by sorry
