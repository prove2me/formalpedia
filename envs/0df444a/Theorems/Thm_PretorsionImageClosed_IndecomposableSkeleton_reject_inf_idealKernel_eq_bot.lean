-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_inf_idealKernel_eq_bot
-- name    : PretorsionImageClosed.IndecomposableSkeleton.reject_inf_idealKernel_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:13:42.904408+00:00
-- url     : https://prove2.me/theorems/2ed5106a-4d75-4786-b778-6fe9e3f1eb2d
-- title:
--   Indecomposable Skeleton: reject inf ideal Kernel eq bot
-- statement:
--   Mutual one-point submodule generation forces the reject of `C` in
--   `X` to meet the common Jacobson-radical kernel trivially.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L205-L247
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean#L205-L247

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

theorem PretorsionImageClosed.IndecomposableSkeleton.reject_inf_idealKernel_eq_bot
    (C : Set ι) {x y : ι} (hxy : x ≠ y)
    (hX :
      σ.reject C (σ.obj x) ⊓
        σ.pointReject y (σ.obj x) = ⊥)
    (hY :
      σ.reject C (σ.obj y) ⊓
        σ.pointReject x (σ.obj y) = ⊥) :
    σ.reject C (σ.obj x) ⊓
        PretorsionImageClosed.idealKernel
          (Ring.jacobson (Module.End R (σ.obj x))) = ⊥ := by sorry
