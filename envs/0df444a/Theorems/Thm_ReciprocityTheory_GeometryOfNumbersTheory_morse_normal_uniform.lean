-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_morse_normal_uniform
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.morse_normal_uniform
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:53:55.738737+00:00
-- url     : https://prove2.me/theorems/c5255bae-bec8-4825-8c09-4bcb1f25ace8
-- title:
--   Geometry Of Numbers Theory: morse normal uniform
-- statement:
--   The Geometry Of Numbers Theory construction uses the morse normal uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/MorseNormSt.lean#L94-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/MorseNormSt.lean#L94-L171

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.morse_normal_uniform {D : ℕ} {ρ₀ C Λ : ℝ} (hρ₀ : 0 < ρ₀) (hC : 0 ≤ C) (hΛ : 0 ≤ Λ) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, 0 < n → ∀ (lam : Fin D → ℝ) (φ ν : (Fin D → ℂ) → ℝ)
      (f : (Fin D → ℂ) → ℂ), (∀ j, 0 ≤ lam j ∧ lam j ≤ Λ) →
      ContinuousOn φ (Metric.ball 0 ρ₀) → ContinuousOn ν (Metric.ball 0 ρ₀) →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, φ z ≤ ∑ j, lam j * ‖z j‖ ^ 2 + C * ‖z‖ ^ 3) →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, 1 - C * ‖z‖ ≤ ν z) →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, 0 ≤ ν z) →
      DifferentiableOn ℂ f (Metric.ball 0 ρ₀) →
      IntegrableOn (fun z => ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z)
        (Metric.ball (0 : Fin D → ℂ) ρ₀) →
      ‖f 0‖ ^ 2 ≤ M * (n : ℝ) ^ D *
        ∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by sorry
