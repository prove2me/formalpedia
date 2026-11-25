-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_extremal_iff_isRelativeSplitInjective_of_sClosed
-- name    : PretorsionImageClosed.IndecomposableSkeleton.extremal_iff_isRelativeSplitInjective_of_sClosed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:16:39.663802+00:00
-- url     : https://prove2.me/theorems/7114d13a-8be0-45a4-9193-0eedaf0d5c2e
-- title:
--   Indecomposable Skeleton: extremal iff is Relative Split Injective of s Closed
-- statement:
--   For an `s`-closed set and one of its members, deletion fails to
--   regenerate that member exactly when the member is relatively split
--   injective.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitInjective.lean#L273-L279
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitInjective.lean#L273-L279

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

theorem PretorsionImageClosed.IndecomposableSkeleton.extremal_iff_isRelativeSplitInjective_of_sClosed
    (C : Set ι) (x : ι)
    [IsArtinianRing (Module.End R (σ.obj x))]
    (_hC : σ.sClosure.IsClosed C) (_hxC : x ∈ C) :
    x ∉ σ.sClosure (C \ {x}) ↔
      σ.IsRelativeSplitInjective C x := by sorry
