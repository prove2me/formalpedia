-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_extremal_iff_isRelativeSplitProjective_of_qClosed
-- name    : PretorsionImageClosed.IndecomposableSkeleton.extremal_iff_isRelativeSplitProjective_of_qClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:16:29.031678+00:00
-- url     : https://prove2.me/theorems/913f8ce6-114c-444c-854d-7f52427ff7c4
-- title:
--   Indecomposable Skeleton: extremal iff is Relative Split Projective of q Closed
-- statement:
--   The equidistribution paper-context wrapper: `C` is quotient-closed and contains
--   `x`.  The stronger theorem above shows that these two assumptions locate
--   the statement inside the closed set but are not needed by the equivalence.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L372-L378
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L372-L378

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

theorem PretorsionImageClosed.IndecomposableSkeleton.extremal_iff_isRelativeSplitProjective_of_qClosed
    (C : Set ι) (x : ι)
    [IsArtinianRing (Module.End R (σ.obj x))]
    (_hC : σ.qClosure.IsClosed C) (_hxC : x ∈ C) :
    x ∉ σ.qClosure (C \ {x}) ↔
      σ.IsRelativeSplitProjective C x := by sorry
