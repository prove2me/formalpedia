-- Prove2me | Theorems.Thm_PretorsionImageClosed_isIndecomposableModule_iff_nontrivial_and_isLocalRing_end
-- name    : PretorsionImageClosed.isIndecomposableModule_iff_nontrivial_and_isLocalRing_end
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:56:42.580566+00:00
-- url     : https://prove2.me/theorems/8e5d9b18-7c2f-5609-8ea0-7ae4bca833c4
-- title:
--   Pretorsion Image Closed: is Indecomposable Module iff nontrivial and is Local Ring end
-- statement:
--   For a finite-length module, indecomposability is equivalent to being
--   nontrivial and having a local endomorphism ring.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L194-L200
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L194-L200

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

theorem PretorsionImageClosed.isIndecomposableModule_iff_nontrivial_and_isLocalRing_end
    (hM : IsFiniteLength A M) :
    IsIndecomposableModule A M ↔ Nontrivial M ∧ IsLocalRing (Module.End A M) := by sorry
