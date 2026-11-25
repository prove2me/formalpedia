-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_inFac_iff_trace_eq_top
-- name    : PretorsionImageClosed.IndecomposableSkeleton.inFac_iff_trace_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:17:16.564327+00:00
-- url     : https://prove2.me/theorems/5e32e0ef-a86a-5407-9803-7a75607bd814
-- title:
--   Indecomposable Skeleton: in Fac iff trace eq top
-- statement:
--   Quotient generation is equivalent to the trace filling the target
--   module.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L257-L325
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L257-L325

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

theorem PretorsionImageClosed.IndecomposableSkeleton.inFac_iff_trace_eq_top (S : Set ι)
    (X : FGModuleCat.{w} R) :
    σ.InFac S X ↔ σ.trace S X = ⊤ := by sorry
