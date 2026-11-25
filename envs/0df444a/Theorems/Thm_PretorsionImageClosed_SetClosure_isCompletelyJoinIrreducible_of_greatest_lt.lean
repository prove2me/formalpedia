-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_isCompletelyJoinIrreducible_of_greatest_lt
-- name    : PretorsionImageClosed.SetClosure.isCompletelyJoinIrreducible_of_greatest_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:11:39.929089+00:00
-- url     : https://prove2.me/theorems/e9758d86-2e8e-4b73-9c7a-ed693a5066c6
-- title:
--   Set Closure: is Completely Join Irreducible of greatest lt
-- statement:
--   An element with a greatest strict predecessor is completely
--   join-irreducible.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/CompletelyJoinIrreducible.lean#L36-L53
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/CompletelyJoinIrreducible.lean#L36-L53

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

theorem PretorsionImageClosed.SetClosure.isCompletelyJoinIrreducible_of_greatest_lt
    {L : Type*} [CompleteLattice L] {j jₛ : L}
    (hₛ : jₛ < j) (hgreatest : ∀ ⦃a : L⦄, a < j → a ≤ jₛ) :
    IsCompletelyJoinIrreducible j := by sorry
