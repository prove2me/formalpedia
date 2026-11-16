-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_theorem_1_3
-- name    : QTolTest1673.Unified.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:25:24.357561+00:00
-- url     : https://prove2.me/theorems/f4a63b1e-7055-4ca2-b37f-3b8dda351fbe
-- title:
--   Theorem 1.3 — Junta testing at constant codimension
-- statement:
--   Junta testing at constant codimension: for fixed 0<ε1<ε2<1/2 with Γ>0 there is s≥2 such that for all large k, with n=k+s, Q_J = O(log k) and R_J = Ω(k). Restated p. 29, proof pp. 29–30.
--
--   $$Q_J=O(\ln k),\qquad R_J=\Omega(k),\qquad n=k+s.$$
--
--   This result supplies a companion query-complexity conclusion alongside the published unified tester.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - encoding: O, Ω, Θ and sufficiently large k → positive existential constants and an eventual integer threshold, before all varying dimensions and algorithms; reason: these are the stated asymptotic bounds with their required uniformity; constants may depend only on the fixed parameters
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Theorem 1.3, p. 6

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Model

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Theorem 1.3, p.6 and pp.29–30, both halves at the same codimension. -/
theorem theorem_1_3 (e₁ e₂ : ℝ) (h₁ : 0 < e₁) (h₁₂ : e₁ < e₂)
    (h₂ : e₂ < 1/2) (hΓ : 0 < gap e₁ e₂) :
  ∃ s : ℕ, 2 ≤ s ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ K₀ : ℕ, 2 ≤ K₀ ∧ ∀ k ≥ K₀,
      QUpper (junta (k+s) k) e₁ e₂ (C * Real.log k) ∧
      CLower (junta (k+s) k) e₁ e₂ (c*k) := by sorry

end QTolTest1673.Unified.Supplement
