-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_coeff_X_sub_C_differentiableAt_26a00f44276f
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_coeff_X_sub_C_differentiableAt_26a00f44276f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:12.194514+00:00
-- url     : https://prove2.me/theorems/cb31f23c-e260-4ff4-b508-e1b44b8122d5
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel coeff X sub C differentiable At 26a00f44276f: P2 M Ground Theory Heights  Heights Hilbert Samuel coeff X sub C differentiable At 26a00f44276f
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel coeff X sub C differentiable At 26a00f44276f construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel coeff X sub C differentiable At 26a00f44276f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PPieceCoefficientsHolomorphic.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PPieceCoefficientsHolomorphic.lean#L26-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceCoefficientsHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PPieceCoefficientsHolomorphic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Matrix Filter Topology

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_coeff_X_sub_C_differentiableAt_26a00f44276f {d : ℕ} (a : (Fin d → ℂ) → ℂ) (y₀ : Fin d → ℂ)
    (ha : DifferentiableAt ℂ a y₀) (k : ℕ) :
    DifferentiableAt ℂ (fun y => (Polynomial.X - Polynomial.C (a y)).coeff k) y₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«coeff_X_sub_C_differentiableAt» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_coeff_X_sub_C_differentiableAt_26a00f44276f
