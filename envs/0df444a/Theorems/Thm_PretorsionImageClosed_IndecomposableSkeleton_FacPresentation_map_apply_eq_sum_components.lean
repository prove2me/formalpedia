-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_FacPresentation_map_apply_eq_sum_components
-- name    : PretorsionImageClosed.IndecomposableSkeleton.FacPresentation.map_apply_eq_sum_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:14:05.78312+00:00
-- url     : https://prove2.me/theorems/9ff5a682-5bf0-4b01-8015-e2d018d35bf0
-- title:
--   Fac Presentation: map apply eq sum components
-- statement:
--   A quotient presentation is pointwise the sum of its component maps.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L50-L109
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L50-L109

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

theorem PretorsionImageClosed.IndecomposableSkeleton.FacPresentation.map_apply_eq_sum_components
    {S : Set ι} {X : FGModuleCat.{w} R}
    (P : σ.FacPresentation S X)
    [Fintype P.index]
    (z : σ.sumOver P.index P.label) :
    P.map.hom.hom z =
      ∑ t : P.index,
        (P.component σ t).hom.hom
          ((biproduct.π
            (fun t : P.index ↦ σ.obj (P.label t)) t).hom.hom z) := by sorry
