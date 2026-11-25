-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_finite_witness
-- name    : PretorsionImageClosed.IndecomposableSkeleton.qSet_finite_witness
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:34:31.127936+00:00
-- url     : https://prove2.me/theorems/651f767e-6768-45db-a504-184d76b6b581
-- title:
--   Indecomposable Skeleton: q Set finite witness
-- statement:
--   Membership in quotient closure is witnessed by finitely many selected
--   representatives.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Presentations.lean#L252-L265
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Presentations.lean#L252-L265

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

theorem PretorsionImageClosed.IndecomposableSkeleton.qSet_finite_witness {S : Set ι} {j : ι}
    (hj : j ∈ σ.qSet S) :
    ∃ T : Set ι, T.Finite ∧ T ⊆ S ∧ j ∈ σ.qSet T := by sorry
