-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_traceRejectCondition_of_isShortPreexact
-- name    : PretorsionImageClosed.Statement.traceRejectCondition_of_isShortPreexact
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:28:49.223747+00:00
-- url     : https://prove2.me/theorems/0d019e98-ec4a-4a33-9a82-978722586f33
-- title:
--   Statement: trace Reject Condition of is Short Preexact
-- statement:
--   The trace–reject condition at `X` holds as soon as `X` has a short preexact sequence
--   `T' → X → F'` with `T' ∈ T` and `F' ∈ F` (the local form of Theorem 2.12, "only if").
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L169-L276
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L169-L276

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

theorem PretorsionImageClosed.Statement.traceRejectCondition_of_isShortPreexact {T' F' : C} {u : T' ⟶ X} {v : X ⟶ F'}
    (hT' : T.prop T') (hF' : F.prop F') (hs : IsShortPreexact (T.prop ⊓ F.prop) u v) :
    TraceRejectCondition T F X := by sorry
