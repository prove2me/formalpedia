-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_fullyInvariant
-- name    : PretorsionImageClosed.IndecomposableSkeleton.trace_fullyInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:18:33.091115+00:00
-- url     : https://prove2.me/theorems/95036ebb-96ae-4206-9fd7-105b28183048
-- title:
--   Indecomposable Skeleton: trace fully Invariant
-- statement:
--   The trace is stable under every endomorphism of its target.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L616-L619
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L616-L619

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

theorem PretorsionImageClosed.IndecomposableSkeleton.trace_fullyInvariant {S : Set ι}
    (X : FGModuleCat.{w} R) (f : X ⟶ X) :
    Submodule.map f.hom.hom (σ.trace S X) ≤ σ.trace S X := by sorry
