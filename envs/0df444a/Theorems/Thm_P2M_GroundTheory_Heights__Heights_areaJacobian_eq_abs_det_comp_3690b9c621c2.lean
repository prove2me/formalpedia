-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_areaJacobian_eq_abs_det_comp_3690b9c621c2
-- name    : P2M_GroundTheory_Heights__Heights_areaJacobian_eq_abs_det_comp_3690b9c621c2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:44:28.636159+00:00
-- url     : https://prove2.me/theorems/e4c96691-467a-42c7-9a56-f6ac9fb9fcf9
-- title:
--   P2 M Ground Theory Heights  Heights area Jacobian eq abs det comp 3690b9c621c2: P2 M Ground Theory Heights  Heights area Jacobian eq abs det comp 3690b9c621c2
-- statement:
--   The P2 M Ground Theory Heights  Heights area Jacobian eq abs det comp 3690b9c621c2 construction uses the P2 M Ground Theory Heights  Heights area Jacobian eq abs det comp 3690b9c621c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaMultiplicity.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaMultiplicity.lean#L13-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaMultiplicity
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
open MeasureTheory Module Set Filter Function
open scoped ENNReal NNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_areaJacobian_eq_abs_det_comp_3690b9c621c2 {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : F ≃ₗᵢ[ℝ] E) (L : E →ₗ[ℝ] F) :
    areaJacobian L = |LinearMap.det (φ.toLinearIsometry.toLinearMap ∘ₗ L)| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«areaJacobian_eq_abs_det_comp» := P2M_GroundTheory_Heights__Heights_areaJacobian_eq_abs_det_comp_3690b9c621c2
