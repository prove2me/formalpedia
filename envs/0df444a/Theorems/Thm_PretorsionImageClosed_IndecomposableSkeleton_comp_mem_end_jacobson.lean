-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_comp_mem_end_jacobson
-- name    : PretorsionImageClosed.IndecomposableSkeleton.comp_mem_end_jacobson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:10:06.202619+00:00
-- url     : https://prove2.me/theorems/2148557c-68f6-4700-a238-6d8dd797c754
-- title:
--   Indecomposable Skeleton: comp mem end jacobson
-- statement:
--   If `x` and `y` index nonisomorphic representatives, every
--   endomorphism of `X` factoring through `Y` belongs to the Jacobson
--   radical of `End(X)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/QuotientAntiExchange.lean#L140-L153
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/QuotientAntiExchange.lean#L140-L153

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
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

theorem PretorsionImageClosed.IndecomposableSkeleton.comp_mem_end_jacobson {x y : ι} (hxy : x ≠ y)
    (f : σ.obj y ⟶ σ.obj x) (g : σ.obj x ⟶ σ.obj y) :
    f.hom.hom.comp g.hom.hom ∈
      Ring.jacobson (Module.End R (σ.obj x)) := by sorry
