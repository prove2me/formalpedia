-- Prove2me | Theorems.Thm_PretorsionImageClosed_IsLocalRing_eq_zero_or_eq_one_of_isIdempotentElem
-- name    : PretorsionImageClosed.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:57:19.615927+00:00
-- url     : https://prove2.me/theorems/f39e5af0-d7a8-4422-9223-9bd0f962f687
-- title:
--   Is Local Ring: eq zero or eq one of is Idempotent Elem
-- statement:
--   An idempotent of a local ring is `0` or `1`. Mathlib's
--   `IsLocalRing.isUnit_or_isUnit_one_sub_self` is stated over a commutative ring,
--   so the splitting of `1 = a + (1 - a)` is taken here from
--   `IsLocalRing.isUnit_or_isUnit_of_isUnit_add`, which holds over any semiring.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/LocalRingIdempotents.lean#L30-L39
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/LocalRingIdempotents.lean#L30-L39

module
public import Mathlib.RingTheory.LocalRing.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
set_option autoImplicit true
@[expose] public section
public section
open PretorsionImageClosed

theorem PretorsionImageClosed.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
    {R : Type*} [Ring R] [IsLocalRing R] {a : R} (ha : IsIdempotentElem a) :
    a = 0 ∨ a = 1 := by sorry
