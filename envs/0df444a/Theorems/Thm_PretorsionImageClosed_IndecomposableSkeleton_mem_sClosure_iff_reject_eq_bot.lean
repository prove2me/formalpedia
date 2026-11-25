-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_reject_eq_bot
-- name    : PretorsionImageClosed.IndecomposableSkeleton.mem_sClosure_iff_reject_eq_bot
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:38:50.670741+00:00
-- url     : https://prove2.me/theorems/f6d21e3a-cfc8-47ae-94c1-5f725cebcd73
-- title:
--   Indecomposable Skeleton: mem s Closure iff reject eq bot
-- statement:
--   Membership in the submodule closure, expressed by the reject
--   criterion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L567-L569
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L567-L569

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

theorem PretorsionImageClosed.IndecomposableSkeleton.mem_sClosure_iff_reject_eq_bot (S : Set ι) (j : ι) :
    j ∈ σ.sClosure S ↔ σ.reject S (σ.obj j) = ⊥ := by sorry
