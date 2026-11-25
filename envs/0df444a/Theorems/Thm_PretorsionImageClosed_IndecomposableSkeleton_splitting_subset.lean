-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_splitting_subset
-- name    : PretorsionImageClosed.IndecomposableSkeleton.splitting_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T07:34:33.1978+00:00
-- url     : https://prove2.me/theorems/b975d155-f6ff-5a34-8be3-fe4a29afb3f2
-- title:
--   Indecomposable Skeleton: splitting subset
-- statement:
--   **Corollary 4.14(2)**: every generating set of `ind Z` contains the splitting projectives and
--   injectives of `Z`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L324-L328
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L324-L328

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
omit [IsArtinianRing R]

theorem PretorsionImageClosed.IndecomposableSkeleton.splitting_subset {Z : Statement.Subcategory (FGModuleCat.{w} R)} {S : Set ι}
    (hS : σ.iClosure S = σ.indOf Z) :
    {x ∈ σ.indOf Z | IsSplittingProjective Z (σ.obj x) ∨ IsSplittingInjective Z (σ.obj x)} ⊆ S := by sorry
