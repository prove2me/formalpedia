-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_mem_sClosure_diff_iff_relativeSplitInjective
-- name    : PretorsionImageClosed.IndecomposableSkeleton.not_mem_sClosure_diff_iff_relativeSplitInjective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:12:32.668463+00:00
-- url     : https://prove2.me/theorems/e27151ac-1f99-4c14-80a4-03ac4fd5355c
-- title:
--   Indecomposable Skeleton: not mem s Closure diff iff relative Split Injective
-- statement:
--   The split-injective bridge, in a slightly stronger form not requiring
--   `C` itself to be closed.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitInjective.lean#L260-L268
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitInjective.lean#L260-L268

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

theorem PretorsionImageClosed.IndecomposableSkeleton.not_mem_sClosure_diff_iff_relativeSplitInjective
    (C : Set ι) (x : ι)
    [IsArtinianRing (Module.End R (σ.obj x))] :
    x ∉ σ.sClosure (C \ {x}) ↔
      σ.IsRelativeSplitInjective C x := by sorry
