-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_coe_inf
-- name    : PretorsionImageClosed.SetClosure.coe_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:49:31.456948+00:00
-- url     : https://prove2.me/theorems/86545ecb-103b-4d7a-a810-9b4eee3c7b6c
-- title:
--   Set Closure: coe inf
-- statement:
--   The Set Closure construction uses the coe inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L52-L54
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L52-L54

module
public import Mathlib.Order.Grade
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets
set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*}
variable {c : SetClosure E}

theorem PretorsionImageClosed.SetClosure.coe_inf (C D : c.Closeds) :
    ((C ⊓ D : c.Closeds) : Set E) = (C : Set E) ∩ (D : Set E) := by sorry

attribute [defeq] PretorsionImageClosed.SetClosure.coe_inf
