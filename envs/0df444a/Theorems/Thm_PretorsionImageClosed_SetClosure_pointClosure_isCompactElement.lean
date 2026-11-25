-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_pointClosure_isCompactElement
-- name    : PretorsionImageClosed.SetClosure.pointClosure_isCompactElement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:03:58.411592+00:00
-- url     : https://prove2.me/theorems/6528c349-6e23-429c-a55a-65808fee1904
-- title:
--   Set Closure: point Closure is Compact Element
-- statement:
--   Finitarity makes every point closure a compact element of the
--   closed-set lattice.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L26-L75
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L26-L75

module
public import Mathlib.Order.CompactlyGenerated.Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}

theorem PretorsionImageClosed.SetClosure.pointClosure_isCompactElement
    (hfin : c.IsFinitary) (x : E) :
    IsCompactElement (c.pointClosure x) := by sorry
