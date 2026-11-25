-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
-- name    : PretorsionImageClosed.IndecomposableSkeleton.sSet_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:48:14.354281+00:00
-- url     : https://prove2.me/theorems/bed00382-4fdb-42b2-9440-093bd44e15f2
-- title:
--   Indecomposable Skeleton: s Set empty
-- statement:
--   No nonzero indecomposable embeds into the empty selected sum.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L531-L540
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L531-L540

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

theorem PretorsionImageClosed.IndecomposableSkeleton.sSet_empty : σ.sSet ∅ = ∅ := by sorry
