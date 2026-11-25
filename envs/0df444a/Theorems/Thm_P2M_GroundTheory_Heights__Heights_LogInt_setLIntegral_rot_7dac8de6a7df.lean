-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_setLIntegral_rot_7dac8de6a7df
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_setLIntegral_rot_7dac8de6a7df
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:53.386146+00:00
-- url     : https://prove2.me/theorems/16482d89-d099-476e-8211-eb47bdb7c7f7
-- title:
--   P2 M Ground Theory Heights  Heights Log Int set LIntegral rot 7dac8de6a7df: P2 M Ground Theory Heights  Heights Log Int set LIntegral rot 7dac8de6a7df
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int set LIntegral rot 7dac8de6a7df construction uses the P2 M Ground Theory Heights  Heights Log Int set LIntegral rot 7dac8de6a7df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntCircle.lean#L98-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntCircle.lean#L98-L112

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_setLIntegral_rot_7dac8de6a7df {V : Type*} [MeasurableSpace V] (μ : Measure V) [SFinite μ]
    (S : Set V) (hS : MeasurableSet S) (R : ℝ → V → V) (hR : Measurable (Function.uncurry R))
    (hpres : ∀ θ, MeasurePreserving (R θ) μ μ) (hinv : ∀ θ, R θ ⁻¹' S = S)
    (G : V → ENNReal) (hG : Measurable G) :
    ENNReal.ofReal (2 * Real.pi) * ∫⁻ u in S, G u ∂μ =
      ∫⁻ u in S, (∫⁻ θ in Ioc 0 (2 * Real.pi), G (R θ u)) ∂μ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«setLIntegral_rot» := P2M_GroundTheory_Heights__Heights_LogInt_setLIntegral_rot_7dac8de6a7df
