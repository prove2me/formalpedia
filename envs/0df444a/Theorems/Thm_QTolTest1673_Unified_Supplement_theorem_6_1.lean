-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_theorem_6_1
-- name    : QTolTest1673.Unified.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:24:49.275937+00:00
-- url     : https://prove2.me/theorems/28adfa1c-7089-47ca-b60a-5bd250728375
-- title:
--   Theorem 6.1 — Tolerant separation at constant codimension n=k+s
-- statement:
--   Tolerant separation at constant codimension n=k+s: a quantum (nonadaptive) junta tester with error ≤ δ and O((ln C(n,s) + ln(1/δ))/Γ²) queries for every k≥1 and 0<δ<1/3, and every randomized adaptive classical tester with success ≥ 2/3 needs Ω(n/s) queries as k→∞.
--
--   $$Q_J=O\!\left(\frac{\ln\binom{k+s}s+\ln(1/\delta)}{\Gamma^2}\right),\qquad R_J=\Omega((k+s)/s).$$
--
--   This result supplies a companion query-complexity conclusion alongside the published unified tester.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - encoding: O, Ω, Θ and sufficiently large k → positive existential constants and an eventual integer threshold, before all varying dimensions and algorithms; reason: these are the stated asymptotic bounds with their required uniformity; constants may depend only on the fixed parameters
--   - generalization: a quantum O-bound at fixed s and thresholds → one absolute upper-bound constant also uniform in s and the thresholds; reason: equation (6) gives ceil((8/Γ²) ln(2 choose(n,s)/δ)); Γ≤1 and ln(1/δ)>1 absorb the ceiling with a uniform constant
--   - encoding: Algorithm 2 draws independent one-query Fourier samples before its decision → the nonadaptive upper-bound witness repeats a fixed circuit with exactly one query per repetition; reason: fixing the per-circuit query count to one excludes sequential multi-query circuits and realizes the source nonadaptivity
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Theorem 6.1, p. 29

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Model

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Theorem 6.1, p.29: an absolute upper constant and both model bounds. -/
theorem theorem_6_1 :
  ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, 2 ≤ s → ∀ e₁ e₂ : ℝ,
    0 ≤ e₁ → e₁ < e₂ → e₂ < blockMean s → 0 < gap e₁ e₂ →
    (∀ k : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → δ < 1/3 →
      NQUpper (junta (k+s) k) e₁ e₂ δ
        (C * (Real.log (Nat.choose (k+s) s : ℝ) + Real.log (1/δ)) / (gap e₁ e₂)^2)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ k ≥ K₀,
      CLower (junta (k+s) k) e₁ e₂ (c * ((k+s : ℕ) : ℝ) / s)) := by sorry

end QTolTest1673.Unified.Supplement
