-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_inter_ne_zero_of_complex_4bc36446fe62
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_inter_ne_zero_of_complex_4bc36446fe62
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:07.711669+00:00
-- url     : https://prove2.me/theorems/b08c68ed-d752-461a-a743-92b92b9b6676
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Manifold Zeros Complement Connected is Preconnected inter ne zero of complex 4bc36446fe62: P2 M Ground Theory Heights  H
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Manifold Zeros Complement Connected is Preconnected inter ne zero of complex 4bc36446fe62 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Manifold Zeros Complement Connected is Preconnected inter ne zero of complex 4bc36446fe62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PManifoldZerosComplementConnected.lean#L61-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PManifoldZerosComplementConnected.lean#L61-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
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
open Topology Filter Set

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_inter_ne_zero_of_complex_4bc36446fe62 {V : Set ℂ}
    (hVo : IsOpen V) (hV : IsPreconnected V) {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ V) {z₀ : ℂ}
    (hz₀ : z₀ ∈ V) (hφz₀ : φ z₀ ≠ 0) : IsPreconnected (V ∩ {z | φ z ≠ 0}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ManifoldZerosComplementConnected».«isPreconnected_inter_ne_zero_of_complex» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_inter_ne_zero_of_complex_4bc36446fe62
