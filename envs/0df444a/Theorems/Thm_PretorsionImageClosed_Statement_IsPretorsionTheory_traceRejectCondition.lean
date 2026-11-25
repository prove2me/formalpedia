-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_traceRejectCondition
-- name    : PretorsionImageClosed.Statement.IsPretorsionTheory.traceRejectCondition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:27:43.821376+00:00
-- url     : https://prove2.me/theorems/74115e77-1492-4092-88d9-60b7480bb870
-- title:
--   Is Pretorsion Theory: trace Reject Condition
-- statement:
--   Theorem 2.12, the "only if" direction: a pretorsion theory satisfies (2.4)
--   at every object.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L282-L285
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L282-L285

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

theorem PretorsionImageClosed.Statement.IsPretorsionTheory.traceRejectCondition (hP : IsPretorsionTheory T.prop F.prop) (X : C) :
    TraceRejectCondition T F X := by sorry
