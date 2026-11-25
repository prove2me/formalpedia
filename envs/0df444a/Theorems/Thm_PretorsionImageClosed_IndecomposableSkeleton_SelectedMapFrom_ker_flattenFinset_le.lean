-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_SelectedMapFrom_ker_flattenFinset_le
-- name    : PretorsionImageClosed.IndecomposableSkeleton.SelectedMapFrom.ker_flattenFinset_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:17:53.814631+00:00
-- url     : https://prove2.me/theorems/24f7808d-da9d-4b7d-adc1-c0133d447924
-- title:
--   Selected Map From: ker flatten Finset le
-- statement:
--   The kernel of the flattened map is contained in the kernel of each
--   map in the finite family.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L384-L432
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L384-L432

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
open PretorsionImageClosed.IndecomposableSkeleton.SelectedMapFrom

theorem PretorsionImageClosed.IndecomposableSkeleton.SelectedMapFrom.ker_flattenFinset_le
    {S : Set ι} {X : FGModuleCat.{w} R}
    (F : Finset (σ.SelectedMapFrom S X))
    (f : σ.SelectedMapFrom S X) (hf : f ∈ F) :
    LinearMap.ker (flattenFinset σ F).map.hom.hom ≤
      LinearMap.ker f.map.hom.hom := by sorry
