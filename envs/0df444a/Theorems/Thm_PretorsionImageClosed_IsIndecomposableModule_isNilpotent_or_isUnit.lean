-- Prove2me | Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_isNilpotent_or_isUnit
-- name    : PretorsionImageClosed.IsIndecomposableModule.isNilpotent_or_isUnit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:34:18.086134+00:00
-- url     : https://prove2.me/theorems/63cd4037-bfe3-44d0-8169-ab2ef16aa998
-- title:
--   Is Indecomposable Module: is Nilpotent or is Unit
-- statement:
--   Fitting's lemma, restated using units of the endomorphism ring.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L160-L163
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L160-L163

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
variable [IsNoetherian A M] [IsArtinian A M]

theorem PretorsionImageClosed.IsIndecomposableModule.isNilpotent_or_isUnit
    (h : IsIndecomposableModule A M) (f : Module.End A M) :
    IsNilpotent f ∨ IsUnit f := by sorry
