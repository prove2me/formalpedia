-- Prove2me | Theorems.Thm_P2M_PretorsionImageClosed_Statement_TraceRejectCondition_isTrivial_arrow_comp___baf7fd259ffe
-- name    : P2M_PretorsionImageClosed_Statement_TraceRejectCondition_isTrivial_arrow_comp___baf7fd259ffe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:28:54.631053+00:00
-- url     : https://prove2.me/theorems/07ac7e7a-00f2-4cc3-9c9c-b428ad967d87
-- title:
--   P2 M Pretorsion Image Closed Statement Trace Reject Condition is Trivial arrow comp   baf7fd259ffe: P2 M Pretorsion Image Closed Statement Trace Reject Condition is Trivial arrow comp   baf7fd259ffe
-- statement:
--   The P2 M Pretorsion Image Closed Statement Trace Reject Condition is Trivial arrow comp   baf7fd259ffe construction uses the P2 M Pretorsion Image Closed Statement Trace Reject Condition is Trivial arrow comp   baf7fd259ffe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L74-L77
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L74-L77

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

theorem P2M_PretorsionImageClosed_Statement_TraceRejectCondition_isTrivial_arrow_comp___baf7fd259ffe :
    IsTrivial (T.prop ⊓ F.prop) ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)) := by sorry

alias «PretorsionImageClosed».«Statement».«TraceRejectCondition».«isTrivial_arrow_comp_π» := P2M_PretorsionImageClosed_Statement_TraceRejectCondition_isTrivial_arrow_comp___baf7fd259ffe
