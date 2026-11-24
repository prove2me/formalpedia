-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isWeightedHomogeneous_aeval_of_weights_ef9f52113e2f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isWeightedHomogeneous_aeval_of_weights_ef9f52113e2f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:51.215001+00:00
-- url     : https://prove2.me/theorems/9ceae9d2-8591-4aea-ba8d-7f57872f945b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Weighted Homogeneous aeval of weights ef9f52113e2f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Weighted Homogeneous aeval of weights ef9f52113e2f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Weighted Homogeneous aeval of weights ef9f52113e2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogGrad.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogGrad.lean#L36-L40

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isWeightedHomogeneous_aeval_of_weights_ef9f52113e2f {w : σ → M} {ω : τ → M} {e : σ → MvPolynomial τ R}
    (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v)) {p : MvPolynomial σ R} {a : M}
    (hp : IsWeightedHomogeneous w p a) : IsWeightedHomogeneous ω (aeval e p) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isWeightedHomogeneous_aeval_of_weights» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isWeightedHomogeneous_aeval_of_weights_ef9f52113e2f
