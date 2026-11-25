-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_iff_traceRejectCondition
-- name    : PretorsionImageClosed.Statement.isPretorsionTheory_iff_traceRejectCondition
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:56:43.972278+00:00
-- url     : https://prove2.me/theorems/b710fec3-7c03-464f-ae2e-8c54b8039159
-- title:
--   Statement: is Pretorsion Theory iff trace Reject Condition
-- statement:
--   **Theorem 2.12.** For a quotient-closed `T` and a subobject-closed `F`, the
--   pair `(T, F)` is a pretorsion theory iff the trace–reject condition (2.4)
--   holds at every object.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L290-L293
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L290-L293

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

theorem PretorsionImageClosed.Statement.isPretorsionTheory_iff_traceRejectCondition (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed) :
    IsPretorsionTheory T.prop F.prop ↔ ∀ X, TraceRejectCondition T F X := by sorry
