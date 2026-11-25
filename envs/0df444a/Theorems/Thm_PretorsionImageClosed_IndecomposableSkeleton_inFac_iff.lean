-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_inFac_iff
-- name    : PretorsionImageClosed.IndecomposableSkeleton.inFac_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:22:30.116258+00:00
-- url     : https://prove2.me/theorems/bcfe7a1a-546d-4ca5-8d0a-d91db8d4a761
-- title:
--   Indecomposable Skeleton: in Fac iff
-- statement:
--   The Indecomposable Skeleton construction uses the in Fac iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L181-L195
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L181-L195

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

theorem PretorsionImageClosed.IndecomposableSkeleton.inFac_iff (S : Set ι) (X : FGModuleCat.{w} R) :
    σ.InFac S X ↔ Statement.Gen (σ.addOf S) X := by sorry
