-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_TraceRejectCondition_isPrekernel
-- name    : PretorsionImageClosed.Statement.TraceRejectCondition.isPrekernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:27:45.609007+00:00
-- url     : https://prove2.me/theorems/cacb3bb7-16ec-47f1-9f40-cdae87c4e1db
-- title:
--   Trace Reject Condition: is Prekernel
-- statement:
--   When (2.4) holds, `t(X) → X` is a `(T ∩ F)`-prekernel of `X → X/r(X)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L80-L96
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L80-L96

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

theorem PretorsionImageClosed.Statement.TraceRejectCondition.isPrekernel :
    IsPrekernel (T.prop ⊓ F.prop) (T.trace X).arrow (cokernel.π (F.reject X).arrow) := by sorry
