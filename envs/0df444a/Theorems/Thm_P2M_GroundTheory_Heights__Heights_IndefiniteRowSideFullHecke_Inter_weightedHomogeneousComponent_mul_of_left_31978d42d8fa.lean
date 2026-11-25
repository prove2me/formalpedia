-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_weightedHomogeneousComponent_mul_of_left_31978d42d8fa
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_weightedHomogeneousComponent_mul_of_left_31978d42d8fa
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:08.399868+00:00
-- url     : https://prove2.me/theorems/a7bca448-927b-411e-aee9-31df95392aef
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter weighted Homogeneous Component mul of left 31978d42d8fa: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Int
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter weighted Homogeneous Component mul of left 31978d42d8fa construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter weighted Homogeneous Component mul of left 31978d42d8fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogGrad.lean#L56-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogGrad.lean#L56-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogGrad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
variable {σ τ R M : Type*} [CommRing R] [AddCommMonoid M]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_weightedHomogeneousComponent_mul_of_left_31978d42d8fa {M : Type*} [AddCancelCommMonoid M] {w : σ → M}
    {c : MvPolynomial σ R} {m : M} (hc : IsWeightedHomogeneous w c m) (γ : M) (L : MvPolynomial σ R) :
    weightedHomogeneousComponent w (γ + m) (c * L) = c * weightedHomogeneousComponent w γ L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«weightedHomogeneousComponent_mul_of_left» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_weightedHomogeneousComponent_mul_of_left_31978d42d8fa
