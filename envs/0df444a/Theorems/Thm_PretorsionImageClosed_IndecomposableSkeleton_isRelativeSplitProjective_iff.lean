-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_isRelativeSplitProjective_iff
-- name    : PretorsionImageClosed.IndecomposableSkeleton.isRelativeSplitProjective_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T07:06:58.288584+00:00
-- url     : https://prove2.me/theorems/24638023-b195-54bf-8da7-5d8f68db2cd1
-- title:
--   Indecomposable Skeleton: is Relative Split Projective iff
-- statement:
--   The Indecomposable Skeleton construction uses the is Relative Split Projective iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L194-L210
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L194-L210

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
omit [IsArtinianRing R]

theorem PretorsionImageClosed.IndecomposableSkeleton.isRelativeSplitProjective_iff (Z : Statement.Subcategory (FGModuleCat.{w} R)) (x : ι) :
    σ.IsRelativeSplitProjective (σ.indOf Z) x ↔ IsSplittingProjective Z (σ.obj x) := by sorry
