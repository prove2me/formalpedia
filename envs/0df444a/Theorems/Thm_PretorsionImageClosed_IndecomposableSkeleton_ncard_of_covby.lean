-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_ncard_of_covby
-- name    : PretorsionImageClosed.IndecomposableSkeleton.ncard_of_covby
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T07:39:10.272823+00:00
-- url     : https://prove2.me/theorems/14d312ff-e989-4e22-b9d9-245f35312f2b
-- title:
--   Indecomposable Skeleton: ncard of covby
-- statement:
--   **Corollary 4.14(3)**: along a cover, the number of indecomposables grows by one; so for a
--   representation-finite algebra the lattice of image-closed subcategories is graded by size.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L383-L394
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L383-L394

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R] {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
variable [IsArtinianRing R]
variable [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]

theorem PretorsionImageClosed.IndecomposableSkeleton.ncard_of_covby
    {Z Z' : {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed}}
    (h : Z' ⋖ Z) (hfin : (σ.indOf Z.1).Finite) :
    (σ.indOf Z.1).ncard = (σ.indOf Z'.1).ncard + 1 := by sorry
