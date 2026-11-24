-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_tsum_lintegral_le_075e4d26f535
-- name    : P2M_GroundTheory_Heights__Heights_LocalGraphMass_tsum_lintegral_le_075e4d26f535
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:46.706558+00:00
-- url     : https://prove2.me/theorems/66d539b9-5ab4-4f05-9e29-3d9bfba43a1a
-- title:
--   P2 M Ground Theory Heights  Heights Local Graph Mass tsum lintegral le 075e4d26f535: P2 M Ground Theory Heights  Heights Local Graph Mass tsum lintegral le 075e4d26f535
-- statement:
--   The P2 M Ground Theory Heights  Heights Local Graph Mass tsum lintegral le 075e4d26f535 construction uses the P2 M Ground Theory Heights  Heights Local Graph Mass tsum lintegral le 075e4d26f535 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphMass.lean#L137-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphMass.lean#L137-L148

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LocalGraphMass
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LocalGraphMass_tsum_lintegral_le_075e4d26f535 {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → ℝ≥0∞) :
    ∑' k, ∫⁻ x, f k x ∂μ ≤ ∫⁻ x, ∑' k, f k x ∂μ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocalGraphMass».«tsum_lintegral_le» := P2M_GroundTheory_Heights__Heights_LocalGraphMass_tsum_lintegral_le_075e4d26f535
