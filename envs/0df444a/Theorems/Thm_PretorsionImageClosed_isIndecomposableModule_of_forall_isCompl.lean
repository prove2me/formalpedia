-- Prove2me | Theorems.Thm_PretorsionImageClosed_isIndecomposableModule_of_forall_isCompl
-- name    : PretorsionImageClosed.isIndecomposableModule_of_forall_isCompl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:15:11.338633+00:00
-- url     : https://prove2.me/theorems/39914e54-54da-4761-9608-0d426e965313
-- title:
--   Pretorsion Image Closed: is Indecomposable Module of forall is Compl
-- statement:
--   A nontrivial module along none of whose decompositions both summands are
--   nonzero is indecomposable.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L58-L61
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L58-L61

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

theorem PretorsionImageClosed.isIndecomposableModule_of_forall_isCompl [Nontrivial M]
    (h : ∀ N P : Submodule A M, IsCompl N P → N = ⊥ ∨ P = ⊥) :
    IsIndecomposableModule A M := by sorry
