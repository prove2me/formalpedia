-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_lintegral_abs_log_circle_le_d71509c99c48
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_lintegral_abs_log_circle_le_d71509c99c48
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:24.482182+00:00
-- url     : https://prove2.me/theorems/4d0aa49d-e627-4b8b-8363-e37b2caf52bb
-- title:
--   P2 M Ground Theory Heights  Heights Log Int lintegral abs log circle le d71509c99c48: P2 M Ground Theory Heights  Heights Log Int lintegral abs log circle le d71509c99c48
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int lintegral abs log circle le d71509c99c48 construction uses the P2 M Ground Theory Heights  Heights Log Int lintegral abs log circle le d71509c99c48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntCircle.lean#L13-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntCircle.lean#L13-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
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
open MeasureTheory Set
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt

theorem P2M_GroundTheory_Heights__Heights_LogInt_lintegral_abs_log_circle_le_d71509c99c48 (P : Polynomial ℂ) (D d0 : ℕ) (M : ℝ)
    (hD : P.natDegree ≤ D) (hd0 : P.coeff d0 ≠ 0)
    (hM : ∀ θ : ℝ, ‖P.eval (circleMap 0 1 θ)‖ ≤ M) :
    ∫⁻ θ in Ioc 0 (2 * Real.pi), ‖Real.log ‖P.eval (circleMap 0 1 θ)‖‖ₑ ≤
      ENNReal.ofReal (4 * Real.pi * Real.log (max M 1) + 2 * Real.pi * D * Real.log 2 +
        2 * Real.pi * |Real.log ‖P.coeff d0‖|) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«lintegral_abs_log_circle_le» := P2M_GroundTheory_Heights__Heights_LogInt_lintegral_abs_log_circle_le_d71509c99c48
