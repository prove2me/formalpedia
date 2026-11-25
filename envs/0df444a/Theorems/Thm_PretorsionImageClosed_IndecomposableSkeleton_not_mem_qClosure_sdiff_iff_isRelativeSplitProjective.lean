-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_mem_qClosure_sdiff_iff_isRelativeSplitProjective
-- name    : PretorsionImageClosed.IndecomposableSkeleton.not_mem_qClosure_sdiff_iff_isRelativeSplitProjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:12:51.393176+00:00
-- url     : https://prove2.me/theorems/3bfdd798-eb48-40dc-9f4a-db0c23534b69
-- title:
--   Indecomposable Skeleton: not mem q Closure sdiff iff is Relative Split Projective
-- statement:
--   The module-theoretic extremality equivalence.  It holds for an arbitrary
--   selected set `C`; only Artinianness of `End(x)` is used in the difficult
--   implication.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L361-L367
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L361-L367

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

theorem PretorsionImageClosed.IndecomposableSkeleton.not_mem_qClosure_sdiff_iff_isRelativeSplitProjective
    (C : Set ι) (x : ι)
    [IsArtinianRing (Module.End R (σ.obj x))] :
    x ∉ σ.qClosure (C \ {x}) ↔
      σ.IsRelativeSplitProjective C x := by sorry
