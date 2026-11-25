-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_range_le_trace
-- name    : PretorsionImageClosed.IndecomposableSkeleton.range_le_trace
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:35:04.893435+00:00
-- url     : https://prove2.me/theorems/4fa8eeeb-889c-4d59-be5a-64fcb9e2086b
-- title:
--   Indecomposable Skeleton: range le trace
-- statement:
--   The range of every selected map lies in the trace.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L105-L109
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L105-L109

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

theorem PretorsionImageClosed.IndecomposableSkeleton.range_le_trace {S : Set ι} {X : FGModuleCat.{w} R}
    (f : σ.SelectedMapTo S X) :
    LinearMap.range f.map.hom.hom ≤ σ.trace S X := by sorry
