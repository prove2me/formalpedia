-- Prove2me | Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_nontrivial
-- name    : PretorsionImageClosed.IsIndecomposableModule.nontrivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:33:58.459803+00:00
-- url     : https://prove2.me/theorems/f664a8f0-d2a2-4a74-b307-26a3c1d11ab5
-- title:
--   Is Indecomposable Module: nontrivial
-- statement:
--   The Is Indecomposable Module construction uses the nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L63-L65
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L63-L65

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

theorem PretorsionImageClosed.IsIndecomposableModule.nontrivial
    (h : IsIndecomposableModule A M) : Nontrivial M := by sorry
