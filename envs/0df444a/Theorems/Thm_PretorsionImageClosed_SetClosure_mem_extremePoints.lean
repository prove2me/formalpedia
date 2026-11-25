-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_mem_extremePoints
-- name    : PretorsionImageClosed.SetClosure.mem_extremePoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:57:20.149907+00:00
-- url     : https://prove2.me/theorems/3d83e7dc-0e84-4fa4-a0d6-5f47c0411cd7
-- title:
--   Set Closure: mem extreme Points
-- statement:
--   The Set Closure construction uses the mem extreme Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Basic.lean#L58-L60
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Basic.lean#L58-L60

module
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Order.Closure
public import Mathlib.Order.Preorder.Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed
open PretorsionImageClosed.SetClosure
variable {E : Type*} (c : SetClosure E)
variable {c}

theorem PretorsionImageClosed.SetClosure.mem_extremePoints {C : Set E} {x : E} :
    x ∈ c.extremePoints C ↔ x ∈ C ∧ x ∉ c (C \ {x}) := by sorry
