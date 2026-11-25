-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_iClosure_isAntiExchange
-- name    : PretorsionImageClosed.IndecomposableSkeleton.iClosure_isAntiExchange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T07:11:14.466772+00:00
-- url     : https://prove2.me/theorems/0280ce62-7812-432a-86bc-0d9c2b252f2c
-- title:
--   Indecomposable Skeleton: i Closure is Anti Exchange
-- statement:
--   Theorem 4.11: anti-exchange for `icl` follows from anti-exchange for `qcl` and `scl`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L95-L113
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ImageClosure.lean#L95-L113

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

theorem PretorsionImageClosed.IndecomposableSkeleton.iClosure_isAntiExchange (hq : σ.qClosure.IsAntiExchange)
    (hs : σ.sClosure.IsAntiExchange) : σ.iClosure.IsAntiExchange := by sorry
