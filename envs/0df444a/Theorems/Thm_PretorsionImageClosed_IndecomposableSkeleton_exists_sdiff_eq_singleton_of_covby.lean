-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_exists_sdiff_eq_singleton_of_covby
-- name    : PretorsionImageClosed.IndecomposableSkeleton.exists_sdiff_eq_singleton_of_covby
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T07:21:18.366984+00:00
-- url     : https://prove2.me/theorems/8eecd729-71f3-4626-bf89-384ae859a499
-- title:
--   Indecomposable Skeleton: exists sdiff eq singleton of covby
-- statement:
--   **Corollary 4.14(3)**: if `Z'` is covered by `Z` among image-closed subcategories, exactly one
--   indecomposable lies in `Z` but not in `Z'`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L332-L379
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L332-L379

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

theorem PretorsionImageClosed.IndecomposableSkeleton.exists_sdiff_eq_singleton_of_covby
    {Z Z' : {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed}}
    (h : Z' ⋖ Z) : ∃ x, σ.indOf Z.1 \ σ.indOf Z'.1 = {x} := by sorry
