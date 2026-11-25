-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_indOf
-- name    : PretorsionImageClosed.IndecomposableSkeleton.mem_indOf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:54:24.723007+00:00
-- url     : https://prove2.me/theorems/7018db76-ffb3-42ed-be48-921ea8aa2fa7
-- title:
--   Indecomposable Skeleton: mem ind Of
-- statement:
--   The Indecomposable Skeleton construction uses the mem ind Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L149-L150
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Subcategories.lean#L149-L150

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

theorem PretorsionImageClosed.IndecomposableSkeleton.mem_indOf {Z : Statement.Subcategory (FGModuleCat.{w} R)} {i : ι} :
    i ∈ σ.indOf Z ↔ Z.prop (σ.obj i) := by sorry
