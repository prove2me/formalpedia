-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_iClosure_isFinitary
-- name    : PretorsionImageClosed.IndecomposableSkeleton.iClosure_isFinitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T07:12:06.265681+00:00
-- url     : https://prove2.me/theorems/52effcd2-4041-515e-b385-19f828308d8f
-- title:
--   Indecomposable Skeleton: i Closure is Finitary
-- statement:
--   Theorem 4.11: `icl` is finitary.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L81-L86
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L81-L86

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

theorem PretorsionImageClosed.IndecomposableSkeleton.iClosure_isFinitary : σ.iClosure.IsFinitary := by sorry
