-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sSet_iff
-- name    : PretorsionImageClosed.IndecomposableSkeleton.mem_sSet_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:26:37.973102+00:00
-- url     : https://prove2.me/theorems/838d06d0-e531-4232-9a99-588da268bc27
-- title:
--   Indecomposable Skeleton: mem s Set iff
-- statement:
--   (4.2): the submodule closure is `scl(S) = ind Cogen(add S)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L219-L221
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L219-L221

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

theorem PretorsionImageClosed.IndecomposableSkeleton.mem_sSet_iff (S : Set ι) (i : ι) :
    i ∈ σ.sSet S ↔ Statement.Cogen (σ.addOf S) (σ.obj i) := by sorry
