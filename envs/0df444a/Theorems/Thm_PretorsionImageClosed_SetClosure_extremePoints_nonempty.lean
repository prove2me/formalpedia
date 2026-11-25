-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_extremePoints_nonempty
-- name    : PretorsionImageClosed.SetClosure.extremePoints_nonempty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:50:19.343304+00:00
-- url     : https://prove2.me/theorems/73cfdf14-2d7f-5f2c-8cf6-f579375a960e
-- title:
--   Set Closure: extreme Points nonempty
-- statement:
--   Every nonempty closed set in a finite convex geometry has an extreme
--   point.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L193-L201
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L193-L201

module
public import Mathlib.Data.Set.Card
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}

theorem PretorsionImageClosed.SetClosure.extremePoints_nonempty [Finite E]
    (hae : c.IsAntiExchange) (hempty : c.IsClosed ∅)
    {C : Set E} (hC : c.IsClosed C) (hCne : C.Nonempty) :
    (c.extremePoints C).Nonempty := by sorry
