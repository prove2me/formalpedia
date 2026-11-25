-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_kernelSubobject_eq_reject_of_isPrecokernel
-- name    : PretorsionImageClosed.Statement.kernelSubobject_eq_reject_of_isPrecokernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:34:35.459596+00:00
-- url     : https://prove2.me/theorems/118cbf23-4459-4a1e-8e44-60c735760976
-- title:
--   Statement: kernel Subobject eq reject of is Precokernel
-- statement:
--   The kernel of the last map of a short preexact sequence of `X` is the reject of `X`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L157-L165
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L157-L165

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
variable (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed)
include hT hF

theorem PretorsionImageClosed.Statement.kernelSubobject_eq_reject_of_isPrecokernel {T' F' : C} {u : T' ⟶ X} {v : X ⟶ F'}
    (hT' : T.prop T') (hF' : F.prop F') (hv : IsPrecokernel (T.prop ⊓ F.prop) u v) :
    kernelSubobject v = F.reject X := by sorry
