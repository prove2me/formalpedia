-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_isCompactlyGenerated_closeds
-- name    : PretorsionImageClosed.SetClosure.isCompactlyGenerated_closeds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:29:40.384212+00:00
-- url     : https://prove2.me/theorems/450f8bd2-ad52-5289-8d53-a89e1815e9e2
-- title:
--   Set Closure: is Compactly Generated closeds
-- statement:
--   The closed-set lattice of a finitary closure operator is compactly
--   generated; this is the equidistribution paper's algebraicity assertion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L149-L168
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean#L149-L168

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

theorem PretorsionImageClosed.SetClosure.isCompactlyGenerated_closeds
    (hfin : c.IsFinitary) :
    IsCompactlyGenerated c.Closeds := by sorry
