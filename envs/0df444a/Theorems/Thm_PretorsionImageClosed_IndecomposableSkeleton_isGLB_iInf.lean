-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_isGLB_iInf
-- name    : PretorsionImageClosed.IndecomposableSkeleton.isGLB_iInf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T07:46:25.604717+00:00
-- url     : https://prove2.me/theorems/058f4a62-b902-4060-ae21-f9db2d388a7d
-- title:
--   Indecomposable Skeleton: is GLB i Inf
-- statement:
--   Corollary 4.14(1), meets: the intersection of image-closed subcategories is their meet.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L268-L273
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L268-L273

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf

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
omit [IsArtinianRing R] [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]

theorem PretorsionImageClosed.IndecomposableSkeleton.isGLB_iInf (s : Set {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed}) :
    IsGLB s ⟨Statement.Subcategory.iInf (fun Z : s => Z.1.1),
      Statement.Subcategory.IsImageClosed.iInf fun Z => Z.1.2⟩ := by sorry
