-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_mk_eq_trace_of_isPrekernel
-- name    : PretorsionImageClosed.Statement.mk_eq_trace_of_isPrekernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:38:54.074469+00:00
-- url     : https://prove2.me/theorems/eee99e82-600d-5c35-acd4-1921cabfe8fc
-- title:
--   Statement: mk eq trace of is Prekernel
-- statement:
--   The first term of a short preexact sequence of `X` is the trace of `X`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L146-L154
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L146-L154

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPrekernel_mono
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_mono

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

theorem PretorsionImageClosed.Statement.mk_eq_trace_of_isPrekernel {T' F' : C} {u : T' ⟶ X} {v : X ⟶ F'} (hT' : T.prop T')
    (hF' : F.prop F') (hu : IsPrekernel (T.prop ⊓ F.prop) u v) :
    haveI := hu.mono
    Subobject.mk u = T.trace X := by sorry
