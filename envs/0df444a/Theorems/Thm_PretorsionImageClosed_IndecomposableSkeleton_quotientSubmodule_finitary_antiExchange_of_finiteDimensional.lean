-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_quotientSubmodule_finitary_antiExchange_of_finiteDimensional
-- name    : PretorsionImageClosed.IndecomposableSkeleton.quotientSubmodule_finitary_antiExchange_of_finiteDimensional
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:15:58.971065+00:00
-- url     : https://prove2.me/theorems/32e0155b-4207-4614-ae3d-17ba9fece749
-- title:
--   Indecomposable Skeleton: quotient Submodule finitary anti Exchange of finite Dimensional
-- statement:
--   The exact combined content of the equidistribution paper's anti-exchange
--   proposition: both closures are finitary and satisfy anti-exchange.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L322-L332
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L322-L332

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

theorem PretorsionImageClosed.IndecomposableSkeleton.quotientSubmodule_finitary_antiExchange_of_finiteDimensional
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    (σ.qClosure.IsFinitary ∧ σ.qClosure.IsAntiExchange) ∧
      (σ.sClosure.IsFinitary ∧ σ.sClosure.IsAntiExchange) := by sorry
