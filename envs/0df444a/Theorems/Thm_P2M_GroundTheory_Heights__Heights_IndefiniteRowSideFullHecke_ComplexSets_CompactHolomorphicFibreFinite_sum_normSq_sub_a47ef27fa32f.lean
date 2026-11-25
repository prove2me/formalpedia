-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompactHolomorphicFibreFinite_sum_normSq_sub_a47ef27fa32f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompactHolomorphicFibreFinite_sum_normSq_sub_a47ef27fa32f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:09.943802+00:00
-- url     : https://prove2.me/theorems/2b46cb6c-2612-597e-9304-d28efd36da5c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Compact Holomorphic Fibre Finite sum norm Sq sub a47ef27fa32f: P2 M Ground Theory Heights  Heights Indefinite Row Side F
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Compact Holomorphic Fibre Finite sum norm Sq sub a47ef27fa32f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Compact Holomorphic Fibre Finite sum norm Sq sub a47ef27fa32f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCompactHolomorphicFibreFinite.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCompactHolomorphicFibreFinite.lean#L14-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompactHolomorphicFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNonIsolatedFibreCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCompactHolomorphicFibreFinite
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
open Topology Metric Filter
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CompactHolomorphicFibreFinite

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompactHolomorphicFibreFinite_sum_normSq_sub_a47ef27fa32f {k : ℕ} (v p : Fin k → ℂ) :
    ∑ i, Complex.normSq (v i - p i) =
      ∑ i, Complex.normSq (v i) + ∑ i, Complex.normSq (p i) -
        2 * (∑ i, v i * (starRingEnd ℂ) (p i)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«CompactHolomorphicFibreFinite».«sum_normSq_sub» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompactHolomorphicFibreFinite_sum_normSq_sub_a47ef27fa32f
