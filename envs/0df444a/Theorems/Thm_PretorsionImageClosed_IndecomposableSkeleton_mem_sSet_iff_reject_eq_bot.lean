-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sSet_iff_reject_eq_bot
-- name    : PretorsionImageClosed.IndecomposableSkeleton.mem_sSet_iff_reject_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:37:26.017799+00:00
-- url     : https://prove2.me/theorems/02c96263-9c7d-45a0-8fba-6c14b9be8bb1
-- title:
--   Indecomposable Skeleton: mem s Set iff reject eq bot
-- statement:
--   Membership in submodule closure is the reject criterion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L525-L527
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L525-L527

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

theorem PretorsionImageClosed.IndecomposableSkeleton.mem_sSet_iff_reject_eq_bot (S : Set ι) (j : ι) :
    j ∈ σ.sSet S ↔ σ.reject S (σ.obj j) = ⊥ := by sorry
