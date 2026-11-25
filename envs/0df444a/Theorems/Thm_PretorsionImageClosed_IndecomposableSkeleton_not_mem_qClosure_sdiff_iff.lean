-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_mem_qClosure_sdiff_iff
-- name    : PretorsionImageClosed.IndecomposableSkeleton.not_mem_qClosure_sdiff_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T07:07:08.421615+00:00
-- url     : https://prove2.me/theorems/267bb2b1-fae8-5bf2-871d-3223177eea58
-- title:
--   Indecomposable Skeleton: not mem q Closure sdiff iff
-- statement:
--   **Proposition 4.13(1).**
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L235-L238
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L235-L238

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

theorem PretorsionImageClosed.IndecomposableSkeleton.not_mem_qClosure_sdiff_iff (Z : Statement.Subcategory (FGModuleCat.{w} R)) (x : ι) :
    x ∉ σ.qClosure (σ.indOf Z \ {x}) ↔ IsSplittingProjective Z (σ.obj x) := by sorry
