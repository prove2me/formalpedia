-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormBasic_hyps_7712b68f0459
-- name    : P2M_GroundTheory_Heights__Heights_gaussNormBasic_hyps_7712b68f0459
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:40:23.541226+00:00
-- url     : https://prove2.me/theorems/baeba74a-9cf4-55e1-ae7a-f4b79dc6a520
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm Basic hyps 7712b68f0459: P2 M Ground Theory Heights  Heights gauss Norm Basic hyps 7712b68f0459
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm Basic hyps 7712b68f0459 construction uses the P2 M Ground Theory Heights  Heights gauss Norm Basic hyps 7712b68f0459 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L223-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L223-L233

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
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
open MvPolynomial NumberField MeasureTheory ProbabilityTheory TensorProduct ComplexAt
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_gaussNormBasic_hyps_7712b68f0459 :
    (∀ i j, ‖(1 : Matrix (Fin 2) (Fin 2) ℚ_[2]) i j‖ ≤ 1) ∧ (∀ i, ‖(0 : Fin 2 → ℚ_[2]) i‖ ≤ 1) ∧
    IsUnit (1 : Matrix (Fin 2) (Fin 2) ℚ_[2]).det ∧
    (∀ i j, ‖(1 : Matrix (Fin 2) (Fin 2) ℚ_[2])⁻¹ i j‖ ≤ 1) ∧
    (∀ y : Fin 2 → ℚ_[2], (∀ i, ‖y i‖ ≤ 1) → ∃ x : Fin 2 → ℚ_[2], (∀ k, ‖x k‖ ≤ 1) ∧
      (1 : Matrix (Fin 2) (Fin 2) ℚ_[2]).mulVec x = y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNormBasic_hyps» := P2M_GroundTheory_Heights__Heights_gaussNormBasic_hyps_7712b68f0459
