-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_convex_inter_ne_zero_5a3afb509677
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_convex_inter_ne_zero_5a3afb509677
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:49:30.864225+00:00
-- url     : https://prove2.me/theorems/4142cbd3-7eee-4c57-a532-c5657d43b930
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Manifold Zeros Complement Connected is Preconnected convex inter ne zero 5a3afb509677: P2 M Ground Theory Heights  Heigh
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Manifold Zeros Complement Connected is Preconnected convex inter ne zero 5a3afb509677 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Manifold Zeros Complement Connected is Preconnected convex inter ne zero 5a3afb509677 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PManifoldZerosComplementConnected.lean#L96-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PManifoldZerosComplementConnected.lean#L96-L123

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_convex_inter_ne_zero_5a3afb509677 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} (hUo : IsOpen U) (hUc : Convex ℝ U)
    {f : E → ℂ} (hf : AnalyticOnNhd ℂ f U) : IsPreconnected (U ∩ {z | f z ≠ 0}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ManifoldZerosComplementConnected».«isPreconnected_convex_inter_ne_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_convex_inter_ne_zero_5a3afb509677
