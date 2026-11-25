-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qSet_iff_trace_eq_top
-- name    : PretorsionImageClosed.IndecomposableSkeleton.mem_qSet_iff_trace_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:37:12.466746+00:00
-- url     : https://prove2.me/theorems/8401c813-c136-4490-af33-21cabba88913
-- title:
--   Indecomposable Skeleton: mem q Set iff trace eq top
-- statement:
--   Membership in quotient closure is the trace criterion used throughout
--   the equidistribution paper.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L329-L331
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L329-L331

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

theorem PretorsionImageClosed.IndecomposableSkeleton.mem_qSet_iff_trace_eq_top (S : Set ι) (j : ι) :
    j ∈ σ.qSet S ↔ σ.trace S (σ.obj j) = ⊤ := by sorry
