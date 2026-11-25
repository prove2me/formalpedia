-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
-- name    : PretorsionImageClosed.IndecomposableSkeleton.trace_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:46:06.343812+00:00
-- url     : https://prove2.me/theorems/5968504c-f129-4907-8c90-8186c68b8300
-- title:
--   Indecomposable Skeleton: trace empty
-- statement:
--   The trace of the empty selection is zero.  A selected map with no
--   labels has an empty biproduct as its source and is therefore the zero map.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L147-L157
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L147-L157

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

theorem PretorsionImageClosed.IndecomposableSkeleton.trace_empty (X : FGModuleCat.{w} R) :
    σ.trace ∅ X = ⊥ := by sorry
