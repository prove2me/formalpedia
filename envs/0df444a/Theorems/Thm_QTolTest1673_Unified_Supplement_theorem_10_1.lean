-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_theorem_10_1
-- name    : QTolTest1673.Unified.Supplement.theorem_10_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:31:41.72773+00:00
-- url     : https://prove2.me/theorems/8657c8ef-7fa8-4243-bad6-499004ec3e37
-- title:
--   Theorem 10.1 — Exponential quantum lower bound for Fourier dimensionality
-- statement:
--   Exponential quantum lower bound for Fourier dimensionality: for fixed 1/4 ≤ ε1 < ε2 < 5/16, every (ε1,ε2)-tolerant quantum tester for L_{n,k} on n=k+2 variables with success ≥ 2/3 needs Ω(2^{k/4}) queries (constant may depend on the thresholds). This is item 1 of Theorem 1.5 (p. 7).
--
--   $$Q_L=\Omega(2^{k/4}),\qquad n=k+2.$$
--
--   This result supplies a companion query-complexity conclusion alongside the published unified tester.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - encoding: O, Ω, Θ and sufficiently large k → positive existential constants and an eventual integer threshold, before all varying dimensions and algorithms; reason: these are the stated asymptotic bounds with their required uniformity; constants may depend only on the fixed parameters
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Theorem 10.1, p. 47

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Model

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Theorem 10.1, p.47; standard quantum value queries, all adaptive algorithms. -/
theorem theorem_10_1 (e₁ e₂ : ℝ) (h₁ : 1/4 ≤ e₁) (h₁₂ : e₁ < e₂)
    (h₂ : e₂ < 5/16) :
  ∃ c : ℝ, 0 < c ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ k ≥ K₀,
    QLower (linJunta (k+2) k) e₁ e₂ (c * (2 : ℝ)^((k : ℝ)/4)) := by sorry

end QTolTest1673.Unified.Supplement
