-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_isClosed_sdiff_singleton_of_not_mem_closure
-- name    : PretorsionImageClosed.SetClosure.isClosed_sdiff_singleton_of_not_mem_closure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:19:17.210103+00:00
-- url     : https://prove2.me/theorems/c6ba7ee1-f3db-4165-9389-dc2469d23d9e
-- title:
--   Set Closure: is Closed sdiff singleton of not mem closure
-- statement:
--   If deleting `x` from a closed set does not regenerate `x`, the
--   deletion is closed.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Basic.lean#L64-L70
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Basic.lean#L64-L70

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

theorem PretorsionImageClosed.SetClosure.isClosed_sdiff_singleton_of_not_mem_closure
    {C : Set E} {x : E} (hC : c.IsClosed C)
    (hx : x ∉ c (C \ {x})) :
    c.IsClosed (C \ {x}) := by sorry
