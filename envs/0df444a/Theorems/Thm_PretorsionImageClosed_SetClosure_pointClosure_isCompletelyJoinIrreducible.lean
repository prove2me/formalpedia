-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_pointClosure_isCompletelyJoinIrreducible
-- name    : PretorsionImageClosed.SetClosure.pointClosure_isCompletelyJoinIrreducible
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:03:36.634794+00:00
-- url     : https://prove2.me/theorems/ca7ca36c-dc39-5f5a-8a1e-20a47cec3732
-- title:
--   Set Closure: point Closure is Completely Join Irreducible
-- statement:
--   In a finitary convex geometry, a point closure is completely
--   join-irreducible.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/CompletelyJoinIrreducible.lean#L57-L81
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/CompletelyJoinIrreducible.lean#L57-L81

module
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed
open PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}

theorem PretorsionImageClosed.SetClosure.pointClosure_isCompletelyJoinIrreducible
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    (hempty : c.IsClosed ∅) (x : E) :
    IsCompletelyJoinIrreducible (c.pointClosure x) := by sorry
