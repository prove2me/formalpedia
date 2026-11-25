-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_TraceRejectCondition_isPrecokernel
-- name    : PretorsionImageClosed.Statement.TraceRejectCondition.isPrecokernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:28:00.844595+00:00
-- url     : https://prove2.me/theorems/003bca91-d434-4673-bcd2-b0d1d1e39ad8
-- title:
--   Trace Reject Condition: is Precokernel
-- statement:
--   When (2.4) holds, `X → X/r(X)` is a `(T ∩ F)`-precokernel of `t(X) → X`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L99-L114
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L99-L114

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
variable (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed) (h : TraceRejectCondition T F X)
include hT hF h

theorem PretorsionImageClosed.Statement.TraceRejectCondition.isPrecokernel :
    IsPrecokernel (T.prop ⊓ F.prop) (T.trace X).arrow (cokernel.π (F.reject X).arrow) := by sorry
