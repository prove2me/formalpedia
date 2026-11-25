-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qSet_iff
-- name    : PretorsionImageClosed.IndecomposableSkeleton.mem_qSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:26:39.329389+00:00
-- url     : https://prove2.me/theorems/829f2e56-ad75-4aa6-baa6-22667c61eb5d
-- title:
--   Indecomposable Skeleton: mem q Set iff
-- statement:
--   (4.2): the quotient closure is `qcl(S) = ind Gen(add S)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L214-L216
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L214-L216

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

theorem PretorsionImageClosed.IndecomposableSkeleton.mem_qSet_iff (S : Set ι) (i : ι) :
    i ∈ σ.qSet S ↔ Statement.Gen (σ.addOf S) (σ.obj i) := by sorry
