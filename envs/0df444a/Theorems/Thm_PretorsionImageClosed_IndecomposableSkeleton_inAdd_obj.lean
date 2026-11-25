-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_inAdd_obj
-- name    : PretorsionImageClosed.IndecomposableSkeleton.inAdd_obj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:04:05.460798+00:00
-- url     : https://prove2.me/theorems/600b28df-8c75-49ac-99dd-defb0a81f9e0
-- title:
--   Indecomposable Skeleton: in Add obj
-- statement:
--   Every representative in `S` lies in `add S`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L77-L83
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L77-L83

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

theorem PretorsionImageClosed.IndecomposableSkeleton.inAdd_obj {S : Set ι} {i : ι} (hi : i ∈ S) : σ.InAdd S (σ.obj i) := by sorry
