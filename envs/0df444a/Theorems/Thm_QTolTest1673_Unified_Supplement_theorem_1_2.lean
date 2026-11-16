-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_theorem_1_2
-- name    : QTolTest1673.Unified.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:23:13.995703+00:00
-- url     : https://prove2.me/theorems/39815074-f358-4b0c-af82-c32f5201b650
-- title:
--   Theorem 1.2 — Exponential advantage for tolerant Fourier dimensionality testing
-- statement:
--   Exponential advantage for tolerant Fourier dimensionality testing: for fixed 0<ε1<ε2<1/2 with Γ>0 there is s≥2 depending only on ε2 such that for all large k and every n≥k+s, Q_L = O(k) and R_L = Ω(2^{k/2}). Restated p. 26, proof pp. 23–26.
--
--   $$Q_L=O(k),\qquad R_L=\Omega(2^{k/2})\quad(n\ge k+s).$$
--
--   The codimension is chosen from the rejection threshold alone, before the acceptance threshold; the constants and eventual threshold may depend on the fixed thresholds, and are uniform in every larger ambient dimension.
--
--   This result supplies a companion query-complexity conclusion alongside the published unified tester.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - encoding: O, Ω, Θ and sufficiently large k → positive existential constants and an eventual integer threshold, before all varying dimensions and algorithms; reason: these are the stated asymptotic bounds with their required uniformity; constants may depend only on the fixed parameters
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Theorem 1.2, p. 6

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Model

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Theorem 1.2, p.6 and pp.25–26; s depends on e₂ alone. -/
theorem theorem_1_2 :
  ∀ e₂ : ℝ, 0 < e₂ → e₂ < 1/2 → ∃ s : ℕ, 2 ≤ s ∧
    ∀ e₁ : ℝ, 0 < e₁ → e₁ < e₂ → 0 < gap e₁ e₂ →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
        ∀ k ≥ K₀, ∀ n ≥ k+s,
          QUpper (linJunta n k) e₁ e₂ (C*k) ∧
          CLower (linJunta n k) e₁ e₂ (c * (2 : ℝ)^((k : ℝ)/2)) := by sorry

end QTolTest1673.Unified.Supplement
