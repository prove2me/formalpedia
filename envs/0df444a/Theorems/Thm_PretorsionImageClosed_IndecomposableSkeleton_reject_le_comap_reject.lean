-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_le_comap_reject
-- name    : PretorsionImageClosed.IndecomposableSkeleton.reject_le_comap_reject
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:39:49.970627+00:00
-- url     : https://prove2.me/theorems/59cade28-bb27-45d3-ae6c-480a6098b3b6
-- title:
--   Indecomposable Skeleton: reject le comap reject
-- statement:
--   Precomposition carries the reject into the inverse image of the
--   reject.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L590-L613
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L590-L613

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

theorem PretorsionImageClosed.IndecomposableSkeleton.reject_le_comap_reject {S : Set ι}
    {X Y : FGModuleCat.{w} R} (f : X ⟶ Y) :
    σ.reject S X ≤ Submodule.comap f.hom.hom (σ.reject S Y) := by sorry
