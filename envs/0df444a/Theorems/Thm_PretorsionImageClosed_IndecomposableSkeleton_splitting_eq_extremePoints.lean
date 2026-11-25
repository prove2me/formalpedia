-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_splitting_eq_extremePoints
-- name    : PretorsionImageClosed.IndecomposableSkeleton.splitting_eq_extremePoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T07:05:50.813137+00:00
-- url     : https://prove2.me/theorems/22940147-32d1-49d3-898b-b2c573ebd9ab
-- title:
--   Indecomposable Skeleton: splitting eq extreme Points
-- statement:
--   The splitting projectives and injectives of `Z`: `P_Z ∪ I_Z`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L294-L302
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L294-L302

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

theorem PretorsionImageClosed.IndecomposableSkeleton.splitting_eq_extremePoints (Z : Statement.Subcategory (FGModuleCat.{w} R)) :
    {x ∈ σ.indOf Z | IsSplittingProjective Z (σ.obj x) ∨ IsSplittingInjective Z (σ.obj x)} =
      σ.iClosure.extremePoints (σ.indOf Z) := by sorry
