-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_extremePoints_iff_splitting
-- name    : PretorsionImageClosed.IndecomposableSkeleton.extremePoints_iff_splitting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T07:18:47.241801+00:00
-- url     : https://prove2.me/theorems/21af136f-a496-5698-a22f-5edd5c8371f3
-- title:
--   Indecomposable Skeleton: extreme Points iff splitting
-- statement:
--   **Proposition 4.13**, (3) ⇔ (5).
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L257-L262
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L257-L262

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

theorem PretorsionImageClosed.IndecomposableSkeleton.extremePoints_iff_splitting {Z : Statement.Subcategory (FGModuleCat.{w} R)} {x : ι}
    (hx : x ∈ σ.indOf Z) :
    x ∈ σ.iClosure.extremePoints (σ.indOf Z) ↔
      IsSplittingProjective Z (σ.obj x) ∨ IsSplittingInjective Z (σ.obj x) := by sorry
