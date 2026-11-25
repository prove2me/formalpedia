-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_isLUB_join
-- name    : PretorsionImageClosed.IndecomposableSkeleton.isLUB_join
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T07:32:22.132011+00:00
-- url     : https://prove2.me/theorems/4dcb0b43-a758-5030-95de-85a95e4f50ba
-- title:
--   Indecomposable Skeleton: is LUB join
-- statement:
--   Corollary 4.14(1), joins: the join of image-closed subcategories is
--   `icl(add ⋃ Zᵢ)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L278-L290
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L278-L290

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_isLUB_join

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

theorem PretorsionImageClosed.IndecomposableSkeleton.isLUB_join (s : Set {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed}) :
    IsLUB s ⟨σ.addOf (σ.iClosure (⋃ Z ∈ s, σ.indOf Z.1)),
      (σ.isImageClosed_addOf_iff _).2 (σ.iClosure.isClosed_closure _)⟩ := by sorry
