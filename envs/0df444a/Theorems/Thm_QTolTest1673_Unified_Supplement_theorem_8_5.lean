-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_theorem_8_5
-- name    : QTolTest1673.Unified.Supplement.theorem_8_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:29:11.538446+00:00
-- url     : https://prove2.me/theorems/30c46b73-e4ec-4ce8-9706-508521312bd0
-- title:
--   Theorem 8.5 — Linear quantum lower bound for tolerant junta testing
-- statement:
--   Linear quantum lower bound for tolerant junta testing: for 3/8 ≤ ε1 < ε2 ≤ 61/128 and every n ≥ 2k, quantum testers with success ≥ 2/3 need Ω(k) queries; if Γ>0 the quantum query complexity is Θ(k).
--
--   $$Q_J=\Omega(k)\quad(n\ge2k),\qquad \Gamma>0\Longrightarrow Q_J=\Theta(k).$$
--
--   This result supplies a companion query-complexity conclusion alongside the published unified tester.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - encoding: O, Ω, Θ and sufficiently large k → positive existential constants and an eventual integer threshold, before all varying dimensions and algorithms; reason: these are the stated asymptotic bounds with their required uniformity; constants may depend only on the fixed parameters
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Theorem 8.5, p. 39

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Model

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Theorem 8.5, pp.39–41: the entire lower-bound region and conditional upper bound. -/
theorem theorem_8_5 (e₁ e₂ : ℝ) (h₁ : 3/8 ≤ e₁) (h₁₂ : e₁ < e₂)
    (h₂ : e₂ ≤ 61/128) :
  (∃ c : ℝ, 0 < c ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ k ≥ K₀, ∀ n ≥ 2*k,
    QLower (junta n k) e₁ e₂ (c*k)) ∧
  (0 < gap e₁ e₂ → ∃ C : ℝ, 0 < C ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
    ∀ k ≥ K₀, ∀ n ≥ 2*k, QUpper (junta n k) e₁ e₂ (C*k)) := by sorry

end QTolTest1673.Unified.Supplement
