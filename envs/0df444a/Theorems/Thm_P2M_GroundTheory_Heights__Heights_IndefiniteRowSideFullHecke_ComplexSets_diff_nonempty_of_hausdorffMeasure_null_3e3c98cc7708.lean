-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_diff_nonempty_of_hausdorffMeasure_null_3e3c98cc7708
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_diff_nonempty_of_hausdorffMeasure_null_3e3c98cc7708
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:20:58.332821+00:00
-- url     : https://prove2.me/theorems/41340b40-2264-4c47-9fe7-b3f05b993ad9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets diff nonempty of hausdorff Measure null 3e3c98cc7708: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets diff nonempty of hausdorff Measure null 3e3c98cc7708 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets diff nonempty of hausdorff Measure null 3e3c98cc7708 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHausdorffNullComplementConnected.lean#L85-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHausdorffNullComplementConnected.lean#L85-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHausdorffNullComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHausdorffNullComplementConnected
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
open Topology Metric MeasureTheory Set Relation
open scoped NNReal ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_diff_nonempty_of_hausdorffMeasure_null_3e3c98cc7708 [FiniteDimensional ℝ E] {k : ℕ}
    (hk : Module.finrank ℝ E = k + 1) {C : Set E} (hC : μH[(k : ℝ)] C = 0) {U : Set E}
    (hU : IsOpen U) (hne : U.Nonempty) : (U \ C).Nonempty := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«diff_nonempty_of_hausdorffMeasure_null» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_diff_nonempty_of_hausdorffMeasure_null_3e3c98cc7708
