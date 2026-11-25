-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_isCompletelyJoinIrreducible_iff_eq_pointClosure
-- name    : PretorsionImageClosed.SetClosure.isCompletelyJoinIrreducible_iff_eq_pointClosure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:28:08.085205+00:00
-- url     : https://prove2.me/theorems/f0d274e4-daf8-4cc3-8ed1-19fbf445790c
-- title:
--   Set Closure: is Completely Join Irreducible iff eq point Closure
-- statement:
--   The completely join-irreducible closed sets are exactly the point
--   closures.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/CompletelyJoinIrreducible.lean#L85-L108
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/CompletelyJoinIrreducible.lean#L85-L108

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

theorem PretorsionImageClosed.SetClosure.isCompletelyJoinIrreducible_iff_eq_pointClosure
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    (hempty : c.IsClosed ∅) (J : c.Closeds) :
    IsCompletelyJoinIrreducible J ↔
      ∃ x : E, J = c.pointClosure x := by sorry
