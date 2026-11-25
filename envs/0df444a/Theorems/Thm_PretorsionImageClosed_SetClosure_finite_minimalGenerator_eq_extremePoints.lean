-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_finite_minimalGenerator_eq_extremePoints
-- name    : PretorsionImageClosed.SetClosure.finite_minimalGenerator_eq_extremePoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:04:15.129295+00:00
-- url     : https://prove2.me/theorems/f2d4310e-cf95-5e94-8b60-6d3acbd1bc61
-- title:
--   Set Closure: finite minimal Generator eq extreme Points
-- statement:
--   In the finitary setting, every finite minimal generator is the
--   extreme-point set, even when the ambient ground type is infinite.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L243-L289
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L243-L289

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

theorem PretorsionImageClosed.SetClosure.finite_minimalGenerator_eq_extremePoints
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    {B C : Set E} (hC : c.IsClosed C)
    (hB : c.IsMinimalGenerator B C) :
    B = c.extremePoints C := by sorry
