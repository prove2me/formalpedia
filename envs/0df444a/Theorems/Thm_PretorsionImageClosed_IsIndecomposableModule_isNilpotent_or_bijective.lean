-- Prove2me | Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_isNilpotent_or_bijective
-- name    : PretorsionImageClosed.IsIndecomposableModule.isNilpotent_or_bijective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:15:40.795805+00:00
-- url     : https://prove2.me/theorems/85c0d5b6-dbb4-44de-93f5-23a318085604
-- title:
--   Is Indecomposable Module: is Nilpotent or bijective
-- statement:
--   Fitting's lemma: an endomorphism of an indecomposable Noetherian and
--   Artinian module is either nilpotent or bijective.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L137-L157
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L137-L157

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

theorem PretorsionImageClosed.IsIndecomposableModule.isNilpotent_or_bijective
    (h : IsIndecomposableModule A M) (f : Module.End A M) :
    IsNilpotent f ∨ Function.Bijective f := by sorry
