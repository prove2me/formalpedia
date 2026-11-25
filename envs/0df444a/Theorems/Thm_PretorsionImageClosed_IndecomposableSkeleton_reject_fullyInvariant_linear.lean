-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_fullyInvariant_linear
-- name    : PretorsionImageClosed.IndecomposableSkeleton.reject_fullyInvariant_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:12:15.996967+00:00
-- url     : https://prove2.me/theorems/11ede5bf-6f4e-4c3d-94c6-564764ab8ef2
-- title:
--   Indecomposable Skeleton: reject fully Invariant linear
-- statement:
--   The reject is invariant under every underlying endomorphism.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L191-L201
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L191-L201

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

theorem PretorsionImageClosed.IndecomposableSkeleton.reject_fullyInvariant_linear {S : Set ι}
    (X : FGModuleCat.{w} R) (f : Module.End R X) :
    Submodule.map f (σ.reject S X) ≤ σ.reject S X := by sorry
