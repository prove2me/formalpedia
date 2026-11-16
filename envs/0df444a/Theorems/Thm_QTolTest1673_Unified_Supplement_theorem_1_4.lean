-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_theorem_1_4
-- name    : QTolTest1673.Unified.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:29:44.698197+00:00
-- url     : https://prove2.me/theorems/bc4c0387-1116-40bb-bc0e-73005a7d908e
-- title:
--   Theorem 1.4 — Worst-case tightness of the unified upper bound
-- statement:
--   Worst-case tightness of the unified upper bound: Q_L = Θ(k) for every fixed 0 ≤ ε1 < ε2 < 1/4 with Γ>0 and every n>k; Q_J = Θ(k) for every fixed 3/8 ≤ ε1 < ε2 ≤ 61/128 with Γ>0 and every n ≥ 2k. Proved by Corollary 7.2 (pp. 30–31) and Theorem 8.5 (pp. 39–41).
--
--   $$Q_L=\Theta(k)\quad(n>k),\qquad Q_J=\Theta(k)\quad(n\ge2k),$$ with the respective threshold ranges stated above.
--
--   This result supplies a companion query-complexity conclusion alongside the published unified tester.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - encoding: O, Ω, Θ and sufficiently large k → positive existential constants and an eventual integer threshold, before all varying dimensions and algorithms; reason: these are the stated asymptotic bounds with their required uniformity; constants may depend only on the fixed parameters
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Theorem 1.4, p. 7

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Model

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Theorem 1.4, p.7: both Θ(k) statements, uniform in n. -/
theorem theorem_1_4 :
  (∀ e₁ e₂ : ℝ, 0 ≤ e₁ → e₁ < e₂ → e₂ < 1/4 → 0 < gap e₁ e₂ →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
      ∀ k ≥ K₀, ∀ n : ℕ, k < n →
        QLower (linJunta n k) e₁ e₂ (c*k) ∧ QUpper (linJunta n k) e₁ e₂ (C*k)) ∧
  (∀ e₁ e₂ : ℝ, 3/8 ≤ e₁ → e₁ < e₂ → e₂ ≤ 61/128 → 0 < gap e₁ e₂ →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
      ∀ k ≥ K₀, ∀ n ≥ 2*k,
        QLower (junta n k) e₁ e₂ (c*k) ∧ QUpper (junta n k) e₁ e₂ (C*k)) := by sorry

end QTolTest1673.Unified.Supplement
