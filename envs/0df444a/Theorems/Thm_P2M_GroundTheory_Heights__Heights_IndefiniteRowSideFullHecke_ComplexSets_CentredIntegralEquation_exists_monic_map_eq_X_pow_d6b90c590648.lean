-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_exists_monic_map_eq_X_pow_d6b90c590648
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_exists_monic_map_eq_X_pow_d6b90c590648
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:07.894827+00:00
-- url     : https://prove2.me/theorems/9f163577-2697-5b87-8a68-db6b03b38698
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Centred Integral Equation exists monic map eq X pow d6b90c590648: P2 M Ground Theory Heights  Heights Indefinite Row Sid
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Centred Integral Equation exists monic map eq X pow d6b90c590648 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Centred Integral Equation exists monic map eq X pow d6b90c590648 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermCentredIntegralEquation.lean#L13-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermCentredIntegralEquation.lean#L13-L85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermCentredIntegralEquation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_exists_monic_map_eq_X_pow_d6b90c590648 {R B K : Type*} [CommRing R] [CommRing B] [Field K] [Algebra R B]
    [Module.Finite R B] (ε : R →+* K) (κ : K →+* R) (hεκ : ∀ c, ε (κ c) = c) (x : B)
    (hx : ∀ c : K, c ≠ 0 → ∀ y : B, IsUnit (algebraMap R B (κ c) + x * y)) :
    ∃ Q : R[X], Q.Monic ∧ aeval x Q = 0 ∧ Q.map ε = X ^ Q.natDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«CentredIntegralEquation».«exists_monic_map_eq_X_pow» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_exists_monic_map_eq_X_pow_d6b90c590648
