-- Prove2me | Theorems.Thm_PretorsionImageClosed_isArtinianRing_end_mod
-- name    : PretorsionImageClosed.isArtinianRing_end_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T07:53:49.116802+00:00
-- url     : https://prove2.me/theorems/ae7beb83-58e8-4c33-a136-8d1a05b8e678
-- title:
--   Pretorsion Image Closed: is Artinian Ring end mod
-- statement:
--   The endomorphism ring of a finite-dimensional `Λ`-module is Artinian.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/FiniteDimensionalAlgebras.lean#L39-L48
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/FiniteDimensionalAlgebras.lean#L39-L48

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Decomposition
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_FiniteDimensionalAlgebras
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open CategoryTheory
open PretorsionImageClosed
universe u

theorem PretorsionImageClosed.isArtinianRing_end_mod (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ]
    (X : FGModuleCat.{u} Λᵐᵒᵖ) :
    IsArtinianRing (Module.End Λᵐᵒᵖ X) := by sorry
