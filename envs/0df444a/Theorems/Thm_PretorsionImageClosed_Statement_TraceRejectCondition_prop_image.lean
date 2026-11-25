-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_TraceRejectCondition_prop_image
-- name    : PretorsionImageClosed.Statement.TraceRejectCondition.prop_image
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:33:57.360438+00:00
-- url     : https://prove2.me/theorems/878e35b0-8a0e-5e20-9a21-eb76dabc4398
-- title:
--   Trace Reject Condition: prop image
-- statement:
--   When (2.4) holds, `t(X)/r(X)` lies in `T ∩ F`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L67-L72
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L67-L72

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

theorem PretorsionImageClosed.Statement.TraceRejectCondition.prop_image :
    (T.prop ⊓ F.prop)
      (imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)) : C) := by sorry
