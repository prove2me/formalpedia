-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_fullyInvariant_linear
-- name    : PretorsionImageClosed.IndecomposableSkeleton.trace_fullyInvariant_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:11:49.33513+00:00
-- url     : https://prove2.me/theorems/520ef879-c84f-4146-a635-e0cded30e91c
-- title:
--   Indecomposable Skeleton: trace fully Invariant linear
-- statement:
--   The selected trace is fully invariant under every underlying
--   endomorphism, not just an endomorphism already presented categorically.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/QuotientAntiExchange.lean#L112-L121
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/QuotientAntiExchange.lean#L112-L121

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

theorem PretorsionImageClosed.IndecomposableSkeleton.trace_fullyInvariant_linear {S : Set ι}
    (X : FGModuleCat.{w} R) (f : Module.End R X) :
    Submodule.map f (σ.trace S X) ≤ σ.trace S X := by sorry
