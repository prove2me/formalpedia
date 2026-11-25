-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isAntiExchange_of_finiteDimensional
-- name    : PretorsionImageClosed.IndecomposableSkeleton.sClosure_isAntiExchange_of_finiteDimensional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:12:10.269103+00:00
-- url     : https://prove2.me/theorems/e5bf449e-4d8b-4e63-a421-caf054118058
-- title:
--   Indecomposable Skeleton: s Closure is Anti Exchange of finite Dimensional
-- statement:
--   The equidistribution paper's finite-dimensional-over-a-field hypothesis supplies
--   submodule anti-exchange.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L296-L307
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L296-L307

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

theorem PretorsionImageClosed.IndecomposableSkeleton.sClosure_isAntiExchange_of_finiteDimensional
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    σ.sClosure.IsAntiExchange := by sorry
