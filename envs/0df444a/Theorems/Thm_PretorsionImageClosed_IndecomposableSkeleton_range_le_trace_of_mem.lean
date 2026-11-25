-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_range_le_trace_of_mem
-- name    : PretorsionImageClosed.IndecomposableSkeleton.range_le_trace_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:08:40.266918+00:00
-- url     : https://prove2.me/theorems/21d4a74b-2f34-4340-ac27-7022b9cfa2d2
-- title:
--   Indecomposable Skeleton: range le trace of mem
-- statement:
--   A map from one selected indecomposable has range in the trace.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L629-L650
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L629-L650

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

theorem PretorsionImageClosed.IndecomposableSkeleton.range_le_trace_of_mem {S : Set ι} {i : ι}
    (hi : i ∈ S) {X : FGModuleCat.{w} R}
    (f : σ.obj i ⟶ X) :
    LinearMap.range f.hom.hom ≤ σ.trace S X := by sorry
