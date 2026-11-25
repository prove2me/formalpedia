-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_isRelativeSplitProjective_of_not_mem_qClosure_sdiff
-- name    : PretorsionImageClosed.IndecomposableSkeleton.isRelativeSplitProjective_of_not_mem_qClosure_sdiff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:14:37.961269+00:00
-- url     : https://prove2.me/theorems/24d37615-a4f7-4fe8-836f-90439045559a
-- title:
--   Indecomposable Skeleton: is Relative Split Projective of not mem q Closure sdiff
-- statement:
--   Extremality implies relative split projectivity.  Nilpotence of the
--   Jacobson radical (here obtained from Artinianness of the endomorphism ring)
--   is the extra input needed to discard nonsplit copies of `x` in a source.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L225-L249
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L225-L249

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

theorem PretorsionImageClosed.IndecomposableSkeleton.isRelativeSplitProjective_of_not_mem_qClosure_sdiff
    (C : Set ι) (x : ι)
    [IsArtinianRing (Module.End R (σ.obj x))]
    (hx : x ∉ σ.qClosure (C \ {x})) :
    σ.IsRelativeSplitProjective C x := by sorry
