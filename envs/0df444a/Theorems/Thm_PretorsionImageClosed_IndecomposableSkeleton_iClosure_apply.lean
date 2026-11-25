-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_iClosure_apply
-- name    : PretorsionImageClosed.IndecomposableSkeleton.iClosure_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T07:06:57.348153+00:00
-- url     : https://prove2.me/theorems/eb8f20f1-4f63-4347-8a97-f0dcc8d05be2
-- title:
--   Indecomposable Skeleton: i Closure apply
-- statement:
--   The Indecomposable Skeleton construction uses the i Closure apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L71-L71
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L71-L71

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

theorem PretorsionImageClosed.IndecomposableSkeleton.iClosure_apply (S : Set ι) : σ.iClosure S = σ.qClosure S ∩ σ.sClosure S := by sorry
