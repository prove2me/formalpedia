-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_le_ker_of_mem
-- name    : PretorsionImageClosed.IndecomposableSkeleton.reject_le_ker_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:10:38.322522+00:00
-- url     : https://prove2.me/theorems/b638f344-b48d-580f-adad-e517a6c7cd5e
-- title:
--   Indecomposable Skeleton: reject le ker of mem
-- statement:
--   Every map to a selected indecomposable occurs in the reject
--   intersection.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L39-L60
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L39-L60

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

theorem PretorsionImageClosed.IndecomposableSkeleton.reject_le_ker_of_mem {S : Set ι} {i : ι}
    (hi : i ∈ S) {X : FGModuleCat.{w} R}
    (f : X ⟶ σ.obj i) :
    σ.reject S X ≤ LinearMap.ker f.hom.hom := by sorry
