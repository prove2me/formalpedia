-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_segment_hits_image_null_7f2307f5f41c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_segment_hits_image_null_7f2307f5f41c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:36.876067+00:00
-- url     : https://prove2.me/theorems/4a17e158-b07e-475f-a732-89b3506978f4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets segment hits image null 7f2307f5f41c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets se
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets segment hits image null 7f2307f5f41c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets segment hits image null 7f2307f5f41c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHausdorffNullComplementConnected.lean#L48-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHausdorffNullComplementConnected.lean#L48-L83

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_segment_hits_image_null_7f2307f5f41c {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] {C : Set E} {x : E} (hx : x ∉ C) (ℓ : E →L[ℝ] ℝ) {α : ℝ}
    (hα : α ≠ ℓ x) (g : E →L[ℝ] F) {d : ℝ} (hd : 0 ≤ d) (hC : μH[d] C = 0) :
    μH[d] (g '' {m | ℓ m = α ∧ (segment ℝ x m ∩ C).Nonempty}) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«segment_hits_image_null» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_segment_hits_image_null_7f2307f5f41c
