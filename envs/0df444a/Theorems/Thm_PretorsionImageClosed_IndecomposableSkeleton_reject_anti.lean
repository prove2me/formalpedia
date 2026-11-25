-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_anti
-- name    : PretorsionImageClosed.IndecomposableSkeleton.reject_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:16:44.168042+00:00
-- url     : https://prove2.me/theorems/fd942263-1cd8-5cdd-bf62-25c5efcde854
-- title:
--   Indecomposable Skeleton: reject anti
-- statement:
--   Reject is antitone in the selected representatives.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L132-L142
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L132-L142

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

theorem PretorsionImageClosed.IndecomposableSkeleton.reject_anti {S T : Set ι} (hST : S ⊆ T)
    (X : FGModuleCat.{w} R) :
    σ.reject T X ≤ σ.reject S X := by sorry
