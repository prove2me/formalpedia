-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_cycleIntegral_eq_sum_9e1d366aec79
-- name    : P2M_GroundTheory_Heights__Heights_cycleIntegral_eq_sum_9e1d366aec79
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:37.974471+00:00
-- url     : https://prove2.me/theorems/637a0eef-ab77-4846-9784-064069df1916
-- title:
--   P2 M Ground Theory Heights  Heights cycle Integral eq sum 9e1d366aec79: P2 M Ground Theory Heights  Heights cycle Integral eq sum 9e1d366aec79
-- statement:
--   The P2 M Ground Theory Heights  Heights cycle Integral eq sum 9e1d366aec79 construction uses the P2 M Ground Theory Heights  Heights cycle Integral eq sum 9e1d366aec79 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PCycleIntegralSection.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PCycleIntegralSection.lean#L11-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PCycleIntegralSection
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
open MvPolynomial MeasureTheory
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_cycleIntegral_eq_sum_9e1d366aec79 {n : ℕ} (h : HermNorm n) (Z : ProjCycle ℂ n) (e : ℕ)
    (g : (Fin n → ℂ) → ℝ) :
    cycleIntegral h Z e g = Z.sum (fun W m => (m : ℝ) * coneIntegral h W e g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«cycleIntegral_eq_sum» := P2M_GroundTheory_Heights__Heights_cycleIntegral_eq_sum_9e1d366aec79
