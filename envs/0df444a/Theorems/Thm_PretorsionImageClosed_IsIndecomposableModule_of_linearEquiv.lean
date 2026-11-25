-- Prove2me | Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_of_linearEquiv
-- name    : PretorsionImageClosed.IsIndecomposableModule.of_linearEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:15:04.017811+00:00
-- url     : https://prove2.me/theorems/4f8287ad-8484-44bf-8c86-9f8e7d120138
-- title:
--   Is Indecomposable Module: of linear Equiv
-- statement:
--   Indecomposability transfers along a linear equivalence.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L73-L79
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L73-L79

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
variable (A : Type u) (M : Type v) [Semiring A] [AddCommMonoid M] [Module A M]
variable {A M}

theorem PretorsionImageClosed.IsIndecomposableModule.of_linearEquiv
    {N : Type w} [AddCommMonoid N] [Module A N]
    (h : IsIndecomposableModule A M) (e : M ≃ₗ[A] N) :
    IsIndecomposableModule A N := by sorry
