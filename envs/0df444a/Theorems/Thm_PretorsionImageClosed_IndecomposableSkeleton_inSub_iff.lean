-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_inSub_iff
-- name    : PretorsionImageClosed.IndecomposableSkeleton.inSub_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:25:48.486777+00:00
-- url     : https://prove2.me/theorems/da5a7bee-de41-5816-b9be-d78100892a5a
-- title:
--   Indecomposable Skeleton: in Sub iff
-- statement:
--   The Indecomposable Skeleton construction uses the in Sub iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L197-L211
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L197-L211

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Definitions.Def_PretorsionImageClosed_Subcategories_Biproducts
public import Definitions.Def_PretorsionImageClosed_Statement
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R] {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

theorem PretorsionImageClosed.IndecomposableSkeleton.inSub_iff (S : Set ι) (X : FGModuleCat.{w} R) :
    σ.InSub S X ↔ Statement.Cogen (σ.addOf S) X := by sorry
