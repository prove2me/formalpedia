-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_FacPresentation_range_le_trace_sdiff_sup_idealRange
-- name    : PretorsionImageClosed.IndecomposableSkeleton.FacPresentation.range_le_trace_sdiff_sup_idealRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:14:29.517824+00:00
-- url     : https://prove2.me/theorems/a61d1ce6-8aa8-4ca2-a7d0-c0dd71ac7ab9
-- title:
--   Fac Presentation: range le trace sdiff sup ideal Range
-- statement:
--   A nonsplit quotient presentation from `add C` has range contained in
--   the trace of `C \ {x}` plus the ranges of radical endomorphisms of `x`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L175-L218
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean#L175-L218

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
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
open PretorsionImageClosed.IndecomposableSkeleton.FacPresentation

theorem PretorsionImageClosed.IndecomposableSkeleton.FacPresentation.range_le_trace_sdiff_sup_idealRange
    {C : Set ι} {x : ι}
    (P : σ.FacPresentation C (σ.obj x))
    (hP : ¬ IsSplitEpi P.map) :
    LinearMap.range P.map.hom.hom ≤
      σ.trace (C \ {x}) (σ.obj x) ⊔
        PretorsionImageClosed.idealRange
          (Ring.jacobson (Module.End R (σ.obj x))) := by sorry
