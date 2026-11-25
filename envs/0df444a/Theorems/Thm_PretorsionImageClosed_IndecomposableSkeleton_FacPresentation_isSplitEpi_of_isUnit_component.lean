-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_FacPresentation_isSplitEpi_of_isUnit_component
-- name    : PretorsionImageClosed.IndecomposableSkeleton.FacPresentation.isSplitEpi_of_isUnit_component
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:13:57.979128+00:00
-- url     : https://prove2.me/theorems/1a74aed4-8129-4f92-b694-4c0c3cbe2a86
-- title:
--   Fac Presentation: is Split Epi of is Unit component
-- statement:
--   If one component, transported to an endomorphism of the target
--   representative, is a unit, the whole presentation splits.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L113-L159
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L113-L159

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
open PretorsionImageClosed.IndecomposableSkeleton.FacPresentation

theorem PretorsionImageClosed.IndecomposableSkeleton.FacPresentation.isSplitEpi_of_isUnit_component
    {S : Set ι} {x : ι}
    (P : σ.FacPresentation S (σ.obj x)) (t : P.index)
    (ht : P.label t = x)
    (hunit :
      IsUnit
        ((eqToHom (congrArg σ.obj ht.symm) ≫
          P.component σ t).hom.hom)) :
    IsSplitEpi P.map := by sorry
