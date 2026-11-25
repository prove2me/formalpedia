-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_trace_eq_top
-- name    : PretorsionImageClosed.IndecomposableSkeleton.mem_qClosure_iff_trace_eq_top
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:38:29.652846+00:00
-- url     : https://prove2.me/theorems/a30e7188-856c-4b74-a18a-ef8e76ef83d8
-- title:
--   Indecomposable Skeleton: mem q Closure iff trace eq top
-- statement:
--   Membership in the quotient closure, expressed by the trace criterion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L561-L563
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L561-L563

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

theorem PretorsionImageClosed.IndecomposableSkeleton.mem_qClosure_iff_trace_eq_top (S : Set ι) (j : ι) :
    j ∈ σ.qClosure S ↔ σ.trace S (σ.obj j) = ⊤ := by sorry
