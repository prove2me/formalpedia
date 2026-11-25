-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_morse_normal_bound
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.morse_normal_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:53:32.818513+00:00
-- url     : https://prove2.me/theorems/1de07fb2-4ee3-4e2d-ac6f-e83f84d1e847
-- title:
--   Geometry Of Numbers Theory: morse normal bound
-- statement:
--   The Geometry Of Numbers Theory construction uses the morse normal bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/MorseNormSt.lean#L7-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/MorseNormSt.lean#L7-L92

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_PolydiscSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseNormSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Filter Topology

theorem ReciprocityTheory.GeometryOfNumbersTheory.morse_normal_bound {D : ℕ} {ρ₀ C : ℝ} (hC : 0 ≤ C) (lam : Fin D → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (φ ν : (Fin D → ℂ) → ℝ)
    (hφc : ContinuousOn φ (Metric.ball 0 ρ₀)) (hνc : ContinuousOn ν (Metric.ball 0 ρ₀))
    (hφ : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, φ z ≤ ∑ j, lam j * ‖z j‖ ^ 2 + C * ‖z‖ ^ 3)
    (hν : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, 1 - C * ‖z‖ ≤ ν z)
    (f : (Fin D → ℂ) → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 ρ₀))
    (n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 < R) (hRn : R / Real.sqrt n < ρ₀)
    (hCR : C * (R / Real.sqrt n) < 1) :
    ‖f 0‖ ^ 2 * ((∏ j, discI (lam j) R) / (n : ℝ) ^ D) *
        (Real.exp (-(C * R ^ 3 / Real.sqrt n)) * (1 - C * (R / Real.sqrt n))) ≤
      ∫ z in Metric.ball (0 : Fin D → ℂ) (R / Real.sqrt n),
        ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by sorry
