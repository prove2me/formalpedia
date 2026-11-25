-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_morseGen_uniform
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.morseGen_uniform
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:53:31.395491+00:00
-- url     : https://prove2.me/theorems/2d037121-cbb6-432b-960e-e4fdcc517bb5
-- title:
--   Geometry Of Numbers Theory: morse Gen uniform
-- statement:
--   The Geometry Of Numbers Theory construction uses the morse Gen uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/MorseGenStB.lean#L10-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/MorseGenStB.lean#L10-L97

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseNormSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_TaylorLeviSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenStB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Complex Matrix Unitary
open scoped ComplexOrder

theorem ReciprocityTheory.GeometryOfNumbersTheory.morseGen_uniform {D : ℕ} {ρ₀ K₂ K₃ Lν νmin : ℝ} (hρ₀ : 0 < ρ₀) (hνmin : 0 < νmin) :
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
