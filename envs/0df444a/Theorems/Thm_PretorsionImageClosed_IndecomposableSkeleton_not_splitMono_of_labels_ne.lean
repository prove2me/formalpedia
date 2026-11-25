-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_splitMono_of_labels_ne
-- name    : PretorsionImageClosed.IndecomposableSkeleton.not_splitMono_of_labels_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:12:34.401515+00:00
-- url     : https://prove2.me/theorems/a187b234-5ffc-4bb0-bc0a-8ae95324139b
-- title:
--   Indecomposable Skeleton: not split Mono of labels ne
-- statement:
--   A split embedding of `X` into a sum of indecomposables all distinct
--   from `X` would put the identity in the endomorphism radical.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitInjective.lean#L70-L121
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitInjective.lean#L70-L121

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

theorem PretorsionImageClosed.IndecomposableSkeleton.not_splitMono_of_labels_ne
    {S : Set ι} {x : ι}
    (P : σ.SubPresentation S (σ.obj x))
    (hne : ∀ t, x ≠ P.label t) :
    ¬ Nonempty (SplitMono P.map) := by sorry
