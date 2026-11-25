-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
-- name    : PretorsionImageClosed.IndecomposableSkeleton.reject_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:46:04.23617+00:00
-- url     : https://prove2.me/theorems/72d6185e-e014-4e35-9944-ae41d7b05bc0
-- title:
--   Indecomposable Skeleton: reject empty
-- statement:
--   The reject of the empty selection is the whole module.  Every map to
--   an empty biproduct is zero.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L162-L172
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L162-L172

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

theorem PretorsionImageClosed.IndecomposableSkeleton.reject_empty (X : FGModuleCat.{w} R) :
    σ.reject ∅ X = ⊤ := by sorry
