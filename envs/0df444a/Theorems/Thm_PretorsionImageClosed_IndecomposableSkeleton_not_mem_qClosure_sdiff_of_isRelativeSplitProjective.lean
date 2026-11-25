-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_mem_qClosure_sdiff_of_isRelativeSplitProjective
-- name    : PretorsionImageClosed.IndecomposableSkeleton.not_mem_qClosure_sdiff_of_isRelativeSplitProjective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:14:40.987163+00:00
-- url     : https://prove2.me/theorems/8da33f6e-5f71-4de2-919e-d0d5a68c1262
-- title:
--   Indecomposable Skeleton: not mem q Closure sdiff of is Relative Split Projective
-- statement:
--   Relative split projectivity prevents generation by the other selected
--   representatives.  This direction only uses locality of `End(x)`, which
--   comes from indecomposability and finite length.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L254-L356
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L254-L356

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

theorem PretorsionImageClosed.IndecomposableSkeleton.not_mem_qClosure_sdiff_of_isRelativeSplitProjective
    (C : Set ι) (x : ι)
    (hproj : σ.IsRelativeSplitProjective C x) :
    x ∉ σ.qClosure (C \ {x}) := by sorry
