-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_eq_top_of_forall_hom_eq_zero
-- name    : PretorsionImageClosed.IndecomposableSkeleton.reject_eq_top_of_forall_hom_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:01:17.801815+00:00
-- url     : https://prove2.me/theorems/5fb4f142-1ac7-5cc2-8ed1-01175feb4534
-- title:
--   Indecomposable Skeleton: reject eq top of forall hom eq zero
-- statement:
--   Dually, if all maps from `X` to selected representatives vanish, their
--   reject in `X` is all of `X`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L89-L102
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L89-L102

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

theorem PretorsionImageClosed.IndecomposableSkeleton.reject_eq_top_of_forall_hom_eq_zero
    {S : Set ι} {X : FGModuleCat.{w} R}
    (hzero : ∀ i : ι, i ∈ S → ∀ f : X ⟶ σ.obj i, f = 0) :
    σ.reject S X = ⊤ := by sorry
