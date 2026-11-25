-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isAntiExchange_of_finiteDimensional
-- name    : PretorsionImageClosed.IndecomposableSkeleton.qClosure_isAntiExchange_of_finiteDimensional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:11:51.448409+00:00
-- url     : https://prove2.me/theorems/41225aa0-277b-4fcb-ac1b-443c14e2c684
-- title:
--   Indecomposable Skeleton: q Closure is Anti Exchange of finite Dimensional
-- statement:
--   The equidistribution paper's finite-dimensional-over-a-field hypothesis supplies
--   the Artinian endomorphism rings required for quotient anti-exchange.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/QuotientAntiExchange.lean#L228-L239
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/QuotientAntiExchange.lean#L228-L239

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

theorem PretorsionImageClosed.IndecomposableSkeleton.qClosure_isAntiExchange_of_finiteDimensional
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    σ.qClosure.IsAntiExchange := by sorry
