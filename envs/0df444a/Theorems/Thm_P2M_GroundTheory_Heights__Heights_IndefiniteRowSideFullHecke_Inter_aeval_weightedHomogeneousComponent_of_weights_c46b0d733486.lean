-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_aeval_weightedHomogeneousComponent_of_weights_c46b0d733486
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_aeval_weightedHomogeneousComponent_of_weights_c46b0d733486
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:44.767531+00:00
-- url     : https://prove2.me/theorems/97201cbe-ad91-4595-8e3f-fad93a7d6a7e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter aeval weighted Homogeneous Component of weights c46b0d733486: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Heck
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter aeval weighted Homogeneous Component of weights c46b0d733486 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter aeval weighted Homogeneous Component of weights c46b0d733486 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogGrad.lean#L14-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogGrad.lean#L14-L34

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_aeval_weightedHomogeneousComponent_of_weights_c46b0d733486 (w : σ → M) (ω : τ → M)
    (e : σ → MvPolynomial τ R) (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v)) (m : M)
    (p : MvPolynomial σ R) :
    aeval e (weightedHomogeneousComponent w m p) = weightedHomogeneousComponent ω m (aeval e p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«aeval_weightedHomogeneousComponent_of_weights» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_aeval_weightedHomogeneousComponent_of_weights_c46b0d733486
