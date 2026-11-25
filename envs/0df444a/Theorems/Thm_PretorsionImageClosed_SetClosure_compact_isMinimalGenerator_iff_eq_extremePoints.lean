-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_compact_isMinimalGenerator_iff_eq_extremePoints
-- name    : PretorsionImageClosed.SetClosure.compact_isMinimalGenerator_iff_eq_extremePoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:30:41.282262+00:00
-- url     : https://prove2.me/theorems/28e8a0f1-32ba-4799-a653-bab0ef98a0df
-- title:
--   Set Closure: compact is Minimal Generator iff eq extreme Points
-- statement:
--   For a compact closed set in a finitary convex geometry, a set is a
--   minimal generator exactly when it is the extreme-point set.  In
--   particular, the minimal basis asserted above is unique.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L311-L320
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L311-L320

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

theorem PretorsionImageClosed.SetClosure.compact_isMinimalGenerator_iff_eq_extremePoints
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    {C : c.Closeds} (hcompact : IsCompactElement C) {B : Set E} :
    c.IsMinimalGenerator B (C : Set E) ↔
      B = c.extremePoints (C : Set E) := by sorry
