-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_map_pointTrace_le
-- name    : PretorsionImageClosed.IndecomposableSkeleton.map_pointTrace_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:15:04.439272+00:00
-- url     : https://prove2.me/theorems/43328f5a-1813-561d-af87-ed0f24152446
-- title:
--   Indecomposable Skeleton: map point Trace le
-- statement:
--   Postcomposition sends the point trace of `i` into the point trace
--   of `i`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/QuotientAntiExchange.lean#L125-L135
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/QuotientAntiExchange.lean#L125-L135

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

theorem PretorsionImageClosed.IndecomposableSkeleton.map_pointTrace_le {i : ι}
    {X Y : FGModuleCat.{w} R} (f : X ⟶ Y) :
    Submodule.map f.hom.hom (σ.pointTrace i X) ≤
      σ.pointTrace i Y := by sorry
