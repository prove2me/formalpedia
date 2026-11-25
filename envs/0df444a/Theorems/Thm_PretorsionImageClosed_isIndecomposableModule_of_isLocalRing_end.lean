-- Prove2me | Theorems.Thm_PretorsionImageClosed_isIndecomposableModule_of_isLocalRing_end
-- name    : PretorsionImageClosed.isIndecomposableModule_of_isLocalRing_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:15:14.760808+00:00
-- url     : https://prove2.me/theorems/20a474e2-bab6-548f-8332-98aa2e40bf96
-- title:
--   Pretorsion Image Closed: is Indecomposable Module of is Local Ring end
-- statement:
--   A nonzero module with local endomorphism ring is indecomposable.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L187-L190
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean#L187-L190

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

theorem PretorsionImageClosed.isIndecomposableModule_of_isLocalRing_end [Nontrivial M]
    [IsLocalRing (Module.End A M)] : IsIndecomposableModule A M := by sorry
