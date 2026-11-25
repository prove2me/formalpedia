-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_eq_iff_nonempty_iso
-- name    : PretorsionImageClosed.IndecomposableSkeleton.eq_iff_nonempty_iso
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:57:58.716697+00:00
-- url     : https://prove2.me/theorems/5c9f4113-a801-4eeb-aaba-985610d6fed5
-- title:
--   Indecomposable Skeleton: eq iff nonempty iso
-- statement:
--   The chosen representative family has no isomorphic duplicates.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Skeleton.lean#L95-L100
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Skeleton.lean#L95-L100

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

theorem PretorsionImageClosed.IndecomposableSkeleton.eq_iff_nonempty_iso {i j : ι} :
    i = j ↔ Nonempty (σ.obj i ≅ σ.obj j) := by sorry
