-- Prove2me | Theorems.Thm_PretorsionImageClosed_theorem_4_11
-- name    : PretorsionImageClosed.theorem_4_11
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T07:42:46.764719+00:00
-- url     : https://prove2.me/theorems/c4a836dd-11be-4e61-876c-921b8f04db4c
-- title:
--   Pretorsion Image Closed: theorem 4 11
-- statement:
--   **Theorem 4.11** for `mod Λ`: the image closure on `ind Λ` is a finitary convex geometry
--   whose closed sets are the sets of indecomposables of the image-closed subcategories.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/FiniteDimensionalAlgebras.lean#L60-L73
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/FiniteDimensionalAlgebras.lean#L60-L73

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Decomposition
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_FiniteDimensionalAlgebras
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open CategoryTheory
open PretorsionImageClosed
universe u

theorem PretorsionImageClosed.theorem_4_11 (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ] :
    haveI := Statement.isNoetherianRing_mop k Λ
    (modSkeleton k Λ).iClosure.IsFinitary ∧ (modSkeleton k Λ).iClosure.IsConvexGeometry ∧
      ∀ Z : Statement.Subcategory (Statement.Mod k Λ),
        Z.IsImageClosed ↔ (modSkeleton k Λ).iClosure.IsClosed ((modSkeleton k Λ).indOf Z) := by sorry
