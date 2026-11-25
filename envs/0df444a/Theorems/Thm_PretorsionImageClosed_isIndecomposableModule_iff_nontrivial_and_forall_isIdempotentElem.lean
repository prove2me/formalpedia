-- Prove2me | Theorems.Thm_PretorsionImageClosed_isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem
-- name    : PretorsionImageClosed.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:53:09.733508+00:00
-- url     : https://prove2.me/theorems/5b7eb939-1817-504e-95fe-d19136f137d8
-- title:
--   Pretorsion Image Closed: is Indecomposable Module iff nontrivial and forall is Idempotent Elem
-- statement:
--   Indecomposability is equivalent to nontriviality together with having no
--   idempotent endomorphisms besides `0` and `1`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L113-L117
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L113-L117

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

theorem PretorsionImageClosed.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem :
    IsIndecomposableModule A M ↔
      Nontrivial M ∧ ∀ f : Module.End A M, IsIdempotentElem f → f = 0 ∨ f = 1 := by sorry
