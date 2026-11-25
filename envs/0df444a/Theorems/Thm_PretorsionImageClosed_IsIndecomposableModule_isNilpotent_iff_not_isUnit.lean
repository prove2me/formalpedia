-- Prove2me | Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_isNilpotent_iff_not_isUnit
-- name    : PretorsionImageClosed.IsIndecomposableModule.isNilpotent_iff_not_isUnit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:56:32.834827+00:00
-- url     : https://prove2.me/theorems/30a09485-e51d-5392-9c70-3133c515344f
-- title:
--   Is Indecomposable Module: is Nilpotent iff not is Unit
-- statement:
--   On an indecomposable Noetherian and Artinian module, the non-units of the
--   endomorphism ring are exactly its nilpotents.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L167-L171
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L167-L171

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

theorem PretorsionImageClosed.IsIndecomposableModule.isNilpotent_iff_not_isUnit
    (h : IsIndecomposableModule A M) (f : Module.End A M) :
    IsNilpotent f ↔ ¬ IsUnit f := by sorry
