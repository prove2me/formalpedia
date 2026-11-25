-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_pointClosure_le_iff
-- name    : PretorsionImageClosed.SetClosure.pointClosure_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:49:23.481804+00:00
-- url     : https://prove2.me/theorems/25eceda9-ee47-4f85-a7f5-0054ee6d1137
-- title:
--   Set Closure: point Closure le iff
-- statement:
--   A point closure lies below a closed set exactly when the point lies in
--   that set.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L79-L82
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L79-L82

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

theorem PretorsionImageClosed.SetClosure.pointClosure_le_iff {x : E} {C : c.Closeds} :
    c.pointClosure x ≤ C ↔ x ∈ (C : Set E) := by sorry
