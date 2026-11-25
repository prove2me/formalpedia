-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_morse_general_uniform
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.morse_general_uniform
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:06.107144+00:00
-- url     : https://prove2.me/theorems/fc514860-5cba-4b0e-8db4-420a8f9b6e6d
-- title:
--   Geometry Of Numbers Theory: morse general uniform
-- statement:
--   The Geometry Of Numbers Theory construction uses the morse general uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/MorseGenSt.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/MorseGenSt.lean#L8-L21

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Complex Matrix
open scoped ComplexOrder

theorem ReciprocityTheory.GeometryOfNumbersTheory.morse_general_uniform {D : ℕ} (ρ₀ K₂ K₃ Lν νmin : ℝ) (hρ₀ : 0 < ρ₀) (hνmin : 0 < νmin) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, 0 < n → ∀ (φ ν : (Fin D → ℂ) → ℝ) (f : (Fin D → ℂ) → ℂ),
      ContDiffOn ℝ 3 φ (Metric.ball 0 ρ₀) →
      ‖fderiv ℝ (fderiv ℝ φ) 0‖ ≤ K₂ →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, ‖iteratedFDeriv ℝ 3 φ z‖ ≤ K₃) →
      ContinuousOn ν (Metric.ball 0 ρ₀) → νmin ≤ ν 0 →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, ν 0 - Lν * ‖z‖ ≤ ν z) →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, 0 ≤ ν z) →
      DifferentiableOn ℂ f (Metric.ball 0 ρ₀) →
      IntegrableOn (fun z => ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z)
        (Metric.ball (0 : Fin D → ℂ) ρ₀) →
      ‖f 0‖ ^ 2 * Real.exp (-((n : ℝ) * φ 0)) ≤ M * (n : ℝ) ^ D *
        ∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by sorry
