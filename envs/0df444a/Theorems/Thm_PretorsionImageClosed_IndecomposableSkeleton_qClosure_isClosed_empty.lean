-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isClosed_empty
-- name    : PretorsionImageClosed.IndecomposableSkeleton.qClosure_isClosed_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:37:27.8858+00:00
-- url     : https://prove2.me/theorems/4c6142e0-2fc7-4c2a-9de2-ff654c7c7804
-- title:
--   Indecomposable Skeleton: q Closure is Closed empty
-- statement:
--   The empty set is closed for quotient generation.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L347-L350
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L347-L350

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

theorem PretorsionImageClosed.IndecomposableSkeleton.qClosure_isClosed_empty :
    σ.qClosure.IsClosed ∅ := by sorry
