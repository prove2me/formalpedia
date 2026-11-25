-- Prove2me | Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_eq_zero_or_eq_one_of_isIdempotentElem
-- name    : PretorsionImageClosed.IsIndecomposableModule.eq_zero_or_eq_one_of_isIdempotentElem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:12:40.127313+00:00
-- url     : https://prove2.me/theorems/4c793886-78f9-42d1-8f2d-2d23bf9be70c
-- title:
--   Is Indecomposable Module: eq zero or eq one of is Idempotent Elem
-- statement:
--   The idempotent endomorphisms of an indecomposable module are `0` and `1`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L90-L98
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L90-L98

module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
public import Theorems.Thm_PretorsionImageClosed_IsLocalRing_eq_zero_or_eq_one_of_isIdempotentElem

set_option autoImplicit true
@[expose] public section
public section
open PretorsionImageClosed
universe u v w
variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]

theorem PretorsionImageClosed.IsIndecomposableModule.eq_zero_or_eq_one_of_isIdempotentElem
    (h : IsIndecomposableModule A M) {f : Module.End A M}
    (hf : IsIdempotentElem f) : f = 0 ∨ f = 1 := by sorry
