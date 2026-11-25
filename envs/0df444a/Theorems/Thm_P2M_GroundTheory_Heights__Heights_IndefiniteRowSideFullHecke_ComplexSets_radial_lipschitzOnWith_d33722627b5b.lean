-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_radial_lipschitzOnWith_d33722627b5b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_radial_lipschitzOnWith_d33722627b5b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:35.261834+00:00
-- url     : https://prove2.me/theorems/04592533-2969-4bb7-99e8-0ff2560b6bba
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets radial lipschitz On With d33722627b5b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets r
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets radial lipschitz On With d33722627b5b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets radial lipschitz On With d33722627b5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHausdorffNullComplementConnected.lean#L12-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHausdorffNullComplementConnected.lean#L12-L44

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_radial_lipschitzOnWith_d33722627b5b (x : E) (ℓ : E →L[ℝ] ℝ) {β δ : ℝ} (hδ : 0 < δ) (R : ℝ) :
    ∃ K, LipschitzOnWith K (fun c => x + ((ℓ c - ℓ x) / β)⁻¹ • (c - x))
      {c | δ ≤ (ℓ c - ℓ x) / β ∧ ‖c - x‖ ≤ R} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«radial_lipschitzOnWith» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_radial_lipschitzOnWith_d33722627b5b
