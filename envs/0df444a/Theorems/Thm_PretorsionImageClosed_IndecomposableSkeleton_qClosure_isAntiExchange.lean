-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isAntiExchange
-- name    : PretorsionImageClosed.IndecomposableSkeleton.qClosure_isAntiExchange
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:08:54.716868+00:00
-- url     : https://prove2.me/theorems/3dcb69e7-39e4-5504-a097-cfd944533e0c
-- title:
--   Indecomposable Skeleton: q Closure is Anti Exchange
-- statement:
--   Quotient closure satisfies anti-exchange whenever the relevant
--   endomorphism rings are Artinian.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/QuotientAntiExchange.lean#L181-L217
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/QuotientAntiExchange.lean#L181-L217

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
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

theorem PretorsionImageClosed.IndecomposableSkeleton.qClosure_isAntiExchange
    [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))] :
    σ.qClosure.IsAntiExchange := by sorry
