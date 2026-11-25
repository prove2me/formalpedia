-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_exists_finset_reject_eq
-- name    : PretorsionImageClosed.IndecomposableSkeleton.exists_finset_reject_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:17:57.908513+00:00
-- url     : https://prove2.me/theorems/6c40bddf-956a-4fa1-a88d-33c8fd6cbd15
-- title:
--   Indecomposable Skeleton: exists finset reject eq
-- statement:
--   In an Artinian module, the intersection defining `reject` is already
--   the intersection of finitely many selected-map kernels.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L438-L466
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L438-L466

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

theorem PretorsionImageClosed.IndecomposableSkeleton.exists_finset_reject_eq
    (S : Set ι) (X : FGModuleCat.{w} R)
    (hX : IsFiniteLength R X) :
    ∃ F : Finset (σ.SelectedMapFrom S X),
      (⨅ f ∈ F, LinearMap.ker f.map.hom.hom) =
        σ.reject S X := by sorry
