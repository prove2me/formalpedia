-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_isSpatial_closeds
-- name    : PretorsionImageClosed.SetClosure.isSpatial_closeds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:27:57.14348+00:00
-- url     : https://prove2.me/theorems/9a47ceac-4604-5413-a524-52affad2910a
-- title:
--   Set Closure: is Spatial closeds
-- statement:
--   The closed-set lattice of a finitary convex geometry is spatial.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/CompletelyJoinIrreducible.lean#L111-L129
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/CompletelyJoinIrreducible.lean#L111-L129

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

theorem PretorsionImageClosed.SetClosure.isSpatial_closeds
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    (hempty : c.IsClosed ∅) :
    IsSpatial c.Closeds := by sorry
