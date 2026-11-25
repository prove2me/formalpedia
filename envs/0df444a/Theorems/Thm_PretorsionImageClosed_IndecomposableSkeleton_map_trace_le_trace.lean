-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_map_trace_le_trace
-- name    : PretorsionImageClosed.IndecomposableSkeleton.map_trace_le_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:39:21.932312+00:00
-- url     : https://prove2.me/theorems/8da50416-6559-4c44-8105-fe557a10cbe5
-- title:
--   Indecomposable Skeleton: map trace le trace
-- statement:
--   Postcomposition carries the selected trace into the selected trace.
--   This is the fully invariant property used in the anti-exchange proof.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L573-L586
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L573-L586

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

theorem PretorsionImageClosed.IndecomposableSkeleton.map_trace_le_trace {S : Set ι}
    {X Y : FGModuleCat.{w} R} (f : X ⟶ Y) :
    Submodule.map f.hom.hom (σ.trace S X) ≤ σ.trace S Y := by sorry
