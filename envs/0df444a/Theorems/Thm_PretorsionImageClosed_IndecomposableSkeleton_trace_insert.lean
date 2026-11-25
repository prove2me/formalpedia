-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_insert
-- name    : PretorsionImageClosed.IndecomposableSkeleton.trace_insert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:18:52.056927+00:00
-- url     : https://prove2.me/theorems/c01cb0eb-1db7-584b-a27e-03adaac2ac03
-- title:
--   Indecomposable Skeleton: trace insert
-- statement:
--   Adjoining one indecomposable adds precisely its singleton trace.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L704-L709
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L704-L709

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

theorem PretorsionImageClosed.IndecomposableSkeleton.trace_insert (S : Set ι) (i : ι)
    (X : FGModuleCat.{w} R) :
    σ.trace (insert i S) X =
      σ.trace S X ⊔ σ.trace {i} X := by sorry
