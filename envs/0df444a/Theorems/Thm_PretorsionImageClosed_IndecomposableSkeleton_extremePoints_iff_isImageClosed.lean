-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_extremePoints_iff_isImageClosed
-- name    : PretorsionImageClosed.IndecomposableSkeleton.extremePoints_iff_isImageClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T07:29:56.163026+00:00
-- url     : https://prove2.me/theorems/ce8df4ec-8168-5158-b6b3-a987fafebdb4
-- title:
--   Indecomposable Skeleton: extreme Points iff is Image Closed
-- statement:
--   **Proposition 4.13**, (3) ⇔ (4).
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L249-L253
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L249-L253

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
omit [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]

theorem PretorsionImageClosed.IndecomposableSkeleton.extremePoints_iff_isImageClosed {Z : Statement.Subcategory (FGModuleCat.{w} R)}
    (hZ : Z.IsImageClosed) {x : ι} (hx : x ∈ σ.indOf Z) :
    x ∈ σ.iClosure.extremePoints (σ.indOf Z) ↔ (σ.addOf (σ.indOf Z \ {x})).IsImageClosed := by sorry
