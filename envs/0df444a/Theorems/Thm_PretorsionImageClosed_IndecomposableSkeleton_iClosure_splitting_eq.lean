-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_iClosure_splitting_eq
-- name    : PretorsionImageClosed.IndecomposableSkeleton.iClosure_splitting_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T07:50:47.218262+00:00
-- url     : https://prove2.me/theorems/4d872592-a0e3-5cfc-8b10-061ee0f0698d
-- title:
--   Indecomposable Skeleton: i Closure splitting eq
-- statement:
--   **Corollary 4.14(2)**: an image-closed subcategory with finitely many indecomposables is the
--   image closure of its splitting projectives and injectives.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L306-L319
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L306-L319

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

theorem PretorsionImageClosed.IndecomposableSkeleton.iClosure_splitting_eq {Z : Statement.Subcategory (FGModuleCat.{w} R)}
    (hZ : Z.IsImageClosed) (hfin : (σ.indOf Z).Finite) :
    σ.iClosure
      {x ∈ σ.indOf Z | IsSplittingProjective Z (σ.obj x) ∨ IsSplittingInjective Z (σ.obj x)} =
      σ.indOf Z := by sorry
