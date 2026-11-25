-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_mem_extremePoints_iff_isClosed_sdiff_singleton
-- name    : PretorsionImageClosed.SetClosure.mem_extremePoints_iff_isClosed_sdiff_singleton
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:19:24.650031+00:00
-- url     : https://prove2.me/theorems/e89b154e-c093-43b0-b431-d935276a8fd4
-- title:
--   Set Closure: mem extreme Points iff is Closed sdiff singleton
-- statement:
--   For a point of a closed set, being extreme is equivalent to legal
--   one-point deletion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Basic.lean#L74-L81
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Basic.lean#L74-L81

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

theorem PretorsionImageClosed.SetClosure.mem_extremePoints_iff_isClosed_sdiff_singleton
    {C : Set E} {x : E} (hC : c.IsClosed C) (hxC : x ∈ C) :
    x ∈ c.extremePoints C ↔ c.IsClosed (C \ {x}) := by sorry
