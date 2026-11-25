-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_eq_bot_of_inSub
-- name    : PretorsionImageClosed.IndecomposableSkeleton.reject_eq_bot_of_inSub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:18:21.540935+00:00
-- url     : https://prove2.me/theorems/c412480d-ee10-4617-9e2a-413a79767228
-- title:
--   Indecomposable Skeleton: reject eq bot of in Sub
-- statement:
--   A submodule presentation is itself one of the maps occurring in the
--   reject intersection, so its monicity forces reject to vanish.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L500-L513
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L500-L513

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

theorem PretorsionImageClosed.IndecomposableSkeleton.reject_eq_bot_of_inSub
    (S : Set ι) (X : FGModuleCat.{w} R)
    (hsub : σ.InSub S X) :
    σ.reject S X = ⊥ := by sorry
