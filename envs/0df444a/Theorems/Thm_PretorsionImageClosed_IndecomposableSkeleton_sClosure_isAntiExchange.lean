-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isAntiExchange
-- name    : PretorsionImageClosed.IndecomposableSkeleton.sClosure_isAntiExchange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:11:16.697815+00:00
-- url     : https://prove2.me/theorems/f4cad124-556a-45d6-b062-b5795d0ac005
-- title:
--   Indecomposable Skeleton: s Closure is Anti Exchange
-- statement:
--   Submodule closure satisfies anti-exchange whenever the relevant
--   endomorphism rings are Artinian.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L251-L285
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L251-L285

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
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

theorem PretorsionImageClosed.IndecomposableSkeleton.sClosure_isAntiExchange
    [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))] :
    σ.sClosure.IsAntiExchange := by sorry
