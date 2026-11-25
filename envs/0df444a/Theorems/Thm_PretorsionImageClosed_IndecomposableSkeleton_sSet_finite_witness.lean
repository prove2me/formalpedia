-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_finite_witness
-- name    : PretorsionImageClosed.IndecomposableSkeleton.sSet_finite_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:34:47.813071+00:00
-- url     : https://prove2.me/theorems/c4aebf00-9af6-473a-92ca-2c2fbf5f0f76
-- title:
--   Indecomposable Skeleton: s Set finite witness
-- statement:
--   Membership in submodule closure is witnessed by finitely many selected
--   representatives.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Presentations.lean#L269-L282
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Presentations.lean#L269-L282

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

theorem PretorsionImageClosed.IndecomposableSkeleton.sSet_finite_witness {S : Set ι} {j : ι}
    (hj : j ∈ σ.sSet S) :
    ∃ T : Set ι, T.Finite ∧ T ⊆ S ∧ j ∈ σ.sSet T := by sorry
