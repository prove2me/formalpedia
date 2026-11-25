-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isFinitary
-- name    : PretorsionImageClosed.IndecomposableSkeleton.sClosure_isFinitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:16:50.049543+00:00
-- url     : https://prove2.me/theorems/545d9509-162d-4cd1-a744-971dda6a3505
-- title:
--   Indecomposable Skeleton: s Closure is Finitary
-- statement:
--   Submodule closure is finitary.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Presentations.lean#L290-L292
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Presentations.lean#L290-L292

module
public import Mathlib.CategoryTheory.FintypeCat
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Skeleton
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

theorem PretorsionImageClosed.IndecomposableSkeleton.sClosure_isFinitary : σ.sClosure.IsFinitary := by sorry
