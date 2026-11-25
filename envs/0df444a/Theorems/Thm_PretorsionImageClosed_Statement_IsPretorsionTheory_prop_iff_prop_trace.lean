-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_prop_iff_prop_trace
-- name    : PretorsionImageClosed.Statement.IsPretorsionTheory.prop_iff_prop_trace
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:27:53.761373+00:00
-- url     : https://prove2.me/theorems/d7450ea0-92b9-4edc-9ed6-7049ef85e20e
-- title:
--   Is Pretorsion Theory: prop iff prop trace
-- statement:
--   Corollary 2.13, first formula: `F = {Y : t_T(Y) ∈ T ∩ F}`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L303-L318
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L303-L318

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
variable (hP : IsPretorsionTheory T.prop F.prop)
include hP

theorem PretorsionImageClosed.Statement.IsPretorsionTheory.prop_iff_prop_trace (Y : C) :
    F.prop Y ↔ (T.prop ⊓ F.prop) (T.trace Y : C) := by sorry
