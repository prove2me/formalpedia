-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_inSub_of_reject_eq_bot
-- name    : PretorsionImageClosed.IndecomposableSkeleton.inSub_of_reject_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:18:09.958891+00:00
-- url     : https://prove2.me/theorems/5317718c-d7fc-4204-ac14-aa3349a109ce
-- title:
--   Indecomposable Skeleton: in Sub of reject eq bot
-- statement:
--   Vanishing reject gives an embedding into one selected finite sum.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L469-L496
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L469-L496

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

theorem PretorsionImageClosed.IndecomposableSkeleton.inSub_of_reject_eq_bot
    (S : Set ι) (X : FGModuleCat.{w} R)
    (hX : IsFiniteLength R X)
    (hreject : σ.reject S X = ⊥) :
    σ.InSub S X := by sorry
