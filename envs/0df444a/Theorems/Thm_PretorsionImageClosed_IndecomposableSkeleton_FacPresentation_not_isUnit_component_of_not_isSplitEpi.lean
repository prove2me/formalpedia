-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_FacPresentation_not_isUnit_component_of_not_isSplitEpi
-- name    : PretorsionImageClosed.IndecomposableSkeleton.FacPresentation.not_isUnit_component_of_not_isSplitEpi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:13:49.923685+00:00
-- url     : https://prove2.me/theorems/8463623c-b399-5f0f-bd8d-6f45dcfb6d9d
-- title:
--   Fac Presentation: not is Unit component of not is Split Epi
-- statement:
--   If a presentation does not split, every component labelled by the
--   target representative becomes a nonunit endomorphism after transport.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L163-L171
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L163-L171

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

theorem PretorsionImageClosed.IndecomposableSkeleton.FacPresentation.not_isUnit_component_of_not_isSplitEpi
    {S : Set ι} {x : ι}
    (P : σ.FacPresentation S (σ.obj x))
    (hP : ¬ IsSplitEpi P.map)
    (t : P.index) (ht : P.label t = x) :
    ¬ IsUnit
      ((eqToHom (congrArg σ.obj ht.symm) ≫
        P.component σ t).hom.hom) := by sorry
