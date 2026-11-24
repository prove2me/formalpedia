-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integrableOn_and_integral_of_lintegral_99de7075dac1
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_integrableOn_and_integral_of_lintegral_99de7075dac1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:08.356605+00:00
-- url     : https://prove2.me/theorems/aa29d92b-b6c7-4248-96fe-ca8e53362a0d
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean integrable On and integral of lintegral 99de7075dac1: P2 M Ground Theory Heights  Heights Sphere Mean integrable On and integral of lintegral 99de7075da
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean integrable On and integral of lintegral 99de7075dac1 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean integrable On and integral of lintegral 99de7075dac1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L193-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L193-L204

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
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
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean

theorem P2M_GroundTheory_Heights__Heights_SphereMean_integrableOn_and_integral_of_lintegral_99de7075dac1 {n : ℕ} {B : Set (Fin n → ℂ)}
    (hB : MeasurableSet B) (hBt : volume B ≠ ⊤) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (hnn : ∀ x ∈ B, 0 ≤ f x) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ x in B, ENNReal.ofReal (f x) = ENNReal.ofReal c * volume B) :
    IntegrableOn f B ∧ ∫ x in B, f x = c * volume.real B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«integrableOn_and_integral_of_lintegral» := P2M_GroundTheory_Heights__Heights_SphereMean_integrableOn_and_integral_of_lintegral_99de7075dac1
