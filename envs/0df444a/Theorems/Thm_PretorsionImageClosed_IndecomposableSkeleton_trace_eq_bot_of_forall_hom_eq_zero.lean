-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_eq_bot_of_forall_hom_eq_zero
-- name    : PretorsionImageClosed.IndecomposableSkeleton.trace_eq_bot_of_forall_hom_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:01:32.537647+00:00
-- url     : https://prove2.me/theorems/c59fcefe-520a-4fc4-864e-1b84a4ced7c7
-- title:
--   Indecomposable Skeleton: trace eq bot of forall hom eq zero
-- statement:
--   If all maps from selected representatives to `X` vanish, their trace in
--   `X` is zero.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L72-L85
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L72-L85

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

theorem PretorsionImageClosed.IndecomposableSkeleton.trace_eq_bot_of_forall_hom_eq_zero
    {S : Set ι} {X : FGModuleCat.{w} R}
    (hzero : ∀ i : ι, i ∈ S → ∀ f : σ.obj i ⟶ X, f = 0) :
    σ.trace S X = ⊥ := by sorry
