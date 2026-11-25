-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isFinitary
-- name    : PretorsionImageClosed.IndecomposableSkeleton.qClosure_isFinitary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:16:56.864409+00:00
-- url     : https://prove2.me/theorems/96dcadaf-b48b-4f8e-a442-ec0e22226f0e
-- title:
--   Indecomposable Skeleton: q Closure is Finitary
-- statement:
--   Quotient closure is finitary.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Presentations.lean#L285-L287
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Presentations.lean#L285-L287

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

theorem PretorsionImageClosed.IndecomposableSkeleton.qClosure_isFinitary : σ.qClosure.IsFinitary := by sorry
