-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_splitMono_of_isUnit_component
-- name    : PretorsionImageClosed.IndecomposableSkeleton.splitMono_of_isUnit_component
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:14:38.980895+00:00
-- url     : https://prove2.me/theorems/de86e893-0fab-4770-8369-7af5a9af5ae2
-- title:
--   Indecomposable Skeleton: split Mono of is Unit component
-- statement:
--   If a component of a presentation is an invertible endomorphism of
--   the source representative, then the whole presentation map splits.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitInjective.lean#L125-L159
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitInjective.lean#L125-L159

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

theorem PretorsionImageClosed.IndecomposableSkeleton.splitMono_of_isUnit_component
    {S : Set ι} {x : ι}
    (P : σ.SubPresentation S (σ.obj x))
    (t : P.index) (ht : P.label t = x)
    (hunit :
      IsUnit
        ((P.map ≫
          biproduct.π
              (fun j : P.index ↦ σ.obj (P.label j)) t ≫
            eqToHom (congrArg σ.obj ht)).hom.hom)) :
    Nonempty (SplitMono P.map) := by sorry
