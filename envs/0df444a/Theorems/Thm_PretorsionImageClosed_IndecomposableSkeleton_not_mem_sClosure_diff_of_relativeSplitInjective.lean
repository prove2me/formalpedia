-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_mem_sClosure_diff_of_relativeSplitInjective
-- name    : PretorsionImageClosed.IndecomposableSkeleton.not_mem_sClosure_diff_of_relativeSplitInjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:15:11.393888+00:00
-- url     : https://prove2.me/theorems/103215a1-5384-4081-9fd0-5706296d7f66
-- title:
--   Indecomposable Skeleton: not mem s Closure diff of relative Split Injective
-- statement:
--   Relative split injectivity prevents `x` from embedding into a sum
--   of the other members of `C`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitInjective.lean#L242-L256
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitInjective.lean#L242-L256

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

theorem PretorsionImageClosed.IndecomposableSkeleton.not_mem_sClosure_diff_of_relativeSplitInjective
    (C : Set ι) (x : ι)
    (hrel : σ.IsRelativeSplitInjective C x) :
    x ∉ σ.sClosure (C \ {x}) := by sorry
