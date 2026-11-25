-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_le_ker
-- name    : PretorsionImageClosed.IndecomposableSkeleton.reject_le_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:36:28.667257+00:00
-- url     : https://prove2.me/theorems/065258c2-f021-44fa-9c53-21b24f993968
-- title:
--   Indecomposable Skeleton: reject le ker
-- statement:
--   The reject lies in the kernel of every selected map.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L112-L116
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L112-L116

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

theorem PretorsionImageClosed.IndecomposableSkeleton.reject_le_ker {S : Set ι} {X : FGModuleCat.{w} R}
    (f : σ.SelectedMapFrom S X) :
    σ.reject S X ≤ LinearMap.ker f.map.hom.hom := by sorry
