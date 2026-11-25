-- Prove2me | Theorems.Thm_PretorsionImageClosed_isIndecomposableModule_iff_nontrivial_and_forall_isCompl
-- name    : PretorsionImageClosed.isIndecomposableModule_iff_nontrivial_and_forall_isCompl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:51:14.463971+00:00
-- url     : https://prove2.me/theorems/4648aac8-3556-5808-8b4d-79546f7163a6
-- title:
--   Pretorsion Image Closed: is Indecomposable Module iff nontrivial and forall is Compl
-- statement:
--   `IsIndecomposableModule` restated as the conjunction defining it.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L51-L54
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L51-L54

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

theorem PretorsionImageClosed.isIndecomposableModule_iff_nontrivial_and_forall_isCompl :
    IsIndecomposableModule A M ↔
      Nontrivial M ∧ ∀ N P : Submodule A M, IsCompl N P → N = ⊥ ∨ P = ⊥ := by sorry
