-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_compact_extremePoints_basis
-- name    : PretorsionImageClosed.SetClosure.compact_extremePoints_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:06:19.185713+00:00
-- url     : https://prove2.me/theorems/3d7e0d02-63cb-4495-a328-3b0ec1582cd5
-- title:
--   Set Closure: compact extreme Points basis
-- statement:
--   A compact closed set in a finitary convex geometry has a finite
--   extreme-point set, and that set is its unique minimal generator.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L293-L306
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L293-L306

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

theorem PretorsionImageClosed.SetClosure.compact_extremePoints_basis
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    {C : c.Closeds} (hcompact : IsCompactElement C) :
    (c.extremePoints (C : Set E)).Finite ∧
      c.IsMinimalGenerator (c.extremePoints (C : Set E)) (C : Set E) := by sorry
