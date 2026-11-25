-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_of_traceRejectCondition
-- name    : PretorsionImageClosed.Statement.isPretorsionTheory_of_traceRejectCondition
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:27:42.040857+00:00
-- url     : https://prove2.me/theorems/46f8b8b6-d3ee-5ddd-be90-cc75252353bd
-- title:
--   Statement: is Pretorsion Theory of trace Reject Condition
-- statement:
--   Theorem 2.12, the "if" direction: a pair `(T, F)` with `T` quotient-closed
--   and `F` subobject-closed satisfying (2.4) at every object is a pretorsion
--   theory, with the canonical short preexact sequences `t(X) → X → X/r(X)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L121-L128
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L121-L128

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

theorem PretorsionImageClosed.Statement.isPretorsionTheory_of_traceRejectCondition (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed) (h : ∀ X, TraceRejectCondition T F X) :
    IsPretorsionTheory T.prop F.prop := by sorry
