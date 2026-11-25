-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_obj_injective
-- name    : PretorsionImageClosed.IndecomposableSkeleton.obj_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:58:45.280481+00:00
-- url     : https://prove2.me/theorems/3100e513-e675-4bad-a94d-c92bfb011549
-- title:
--   Indecomposable Skeleton: obj injective
-- statement:
--   Equality of chosen representative objects forces equality of their
--   indices.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Skeleton.lean#L104-L107
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Skeleton.lean#L104-L107

module
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.HopkinsLevitzki
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Skeleton
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
open PretorsionImageClosed.IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

theorem PretorsionImageClosed.IndecomposableSkeleton.obj_injective : Function.Injective σ.obj := by sorry
