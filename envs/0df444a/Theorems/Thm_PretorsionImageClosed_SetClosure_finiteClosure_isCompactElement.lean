-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_finiteClosure_isCompactElement
-- name    : PretorsionImageClosed.SetClosure.finiteClosure_isCompactElement
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:55:53.873876+00:00
-- url     : https://prove2.me/theorems/cb540b96-44e4-4f18-9d36-53ecc7f49d8f
-- title:
--   Set Closure: finite Closure is Compact Element
-- statement:
--   The closure of a finite set is a compact element of the closed-set
--   lattice.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L79-L103
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L79-L103

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

theorem PretorsionImageClosed.SetClosure.finiteClosure_isCompactElement
    (hfin : c.IsFinitary) {B : Set E} (hBfin : B.Finite) :
    IsCompactElement (c.toCloseds B) := by sorry
