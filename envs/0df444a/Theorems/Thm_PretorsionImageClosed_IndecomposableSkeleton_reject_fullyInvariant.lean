-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_fullyInvariant
-- name    : PretorsionImageClosed.IndecomposableSkeleton.reject_fullyInvariant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:18:25.510074+00:00
-- url     : https://prove2.me/theorems/5aae8b12-fd5b-4f49-a631-89325bf4d669
-- title:
--   Indecomposable Skeleton: reject fully Invariant
-- statement:
--   The reject is stable under inverse image by every endomorphism of its
--   source.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L623-L626
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L623-L626

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

theorem PretorsionImageClosed.IndecomposableSkeleton.reject_fullyInvariant {S : Set ι}
    (X : FGModuleCat.{w} R) (f : X ⟶ X) :
    σ.reject S X ≤ Submodule.comap f.hom.hom (σ.reject S X) := by sorry
