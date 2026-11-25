-- Prove2me | Theorems.Thm_PretorsionImageClosed_isIndecomposableModule_of_forall_isIdempotentElem
-- name    : PretorsionImageClosed.isIndecomposableModule_of_forall_isIdempotentElem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:33:19.107927+00:00
-- url     : https://prove2.me/theorems/28c45908-12b9-48cf-a68d-dfb36e80af70
-- title:
--   Pretorsion Image Closed: is Indecomposable Module of forall is Idempotent Elem
-- statement:
--   A nonzero module whose only idempotent endomorphisms are `0` and `1` is
--   indecomposable.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L102-L109
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L102-L109

module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
set_option autoImplicit true
@[expose] public section
public section
open PretorsionImageClosed
universe u v w
variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]

theorem PretorsionImageClosed.isIndecomposableModule_of_forall_isIdempotentElem [Nontrivial M]
    (h : ∀ f : Module.End A M, IsIdempotentElem f → f = 0 ∨ f = 1) :
    IsIndecomposableModule A M := by sorry
