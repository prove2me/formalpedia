-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_prop_iff_prop_cokernel_reject
-- name    : PretorsionImageClosed.Statement.IsPretorsionTheory.prop_iff_prop_cokernel_reject
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:28:46.325019+00:00
-- url     : https://prove2.me/theorems/cd9cecc5-4c31-5ffc-8923-294e52dde0a2
-- title:
--   Is Pretorsion Theory: prop iff prop cokernel reject
-- statement:
--   Corollary 2.13, second formula: `T = {X : X/r_F(X) ∈ T ∩ F}`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L321-L353
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TraceReject.lean#L321-L353

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

theorem PretorsionImageClosed.Statement.IsPretorsionTheory.prop_iff_prop_cokernel_reject (X : C) :
    T.prop X ↔ (T.prop ⊓ F.prop) (cokernel (F.reject X).arrow) := by sorry
