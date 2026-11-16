-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_theorem_11_4
-- name    : QTolTest1673.Unified.Supplement.theorem_11_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:33:47.227772+00:00
-- url     : https://prove2.me/theorems/82a2c5e4-1745-4418-9334-ef58524fe192
-- title:
--   Theorem 11.4 — Superpolynomial quantum lower bound for tolerant junta testing
-- statement:
--   Superpolynomial quantum lower bound for tolerant junta testing: for all large k, with t=⌈log2 k⌉, s=2t, n=k+s and the §11.1 thresholds, Q_J = Ω((n/s)^{t/4}) and Q_J ≥ k^{(1/4−o(1)) log2 k}. Together with Theorem 1.5 item 2 (p. 7): 0<ε1<ε2<1/2, both thresholds tend to 1/2, and ε2−ε1 = 1/(2L²) = Θ(k^{−4}).
--
--   $$Q_J=\Omega((n/s)^{t/4}),\qquad Q_J\ge k^{(1/4-o(1))\log_2k},\qquad\varepsilon_2-\varepsilon_1=\frac1{2L^2}=\Theta(k^{-4}).$$
--
--   Here t, s, n, L and both thresholds are exactly the computed functions in Section 11.1. Both thresholds lie strictly between zero and one half for all sufficiently large k and tend to one half. For every η>0 the exponent lower bound holds with 1/4−η for all sufficiently large k.
--
--   This result supplies a companion query-complexity conclusion alongside the published unified tester.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - encoding: O, Ω, Θ and sufficiently large k → positive existential constants and an eventual integer threshold, before all varying dimensions and algorithms; reason: these are the stated asymptotic bounds with their required uniformity; constants may depend only on the fixed parameters
--   - encoding: the explicit Section 11.1 thresholds, their limits, the Θ(k^(−4)) gap, and the exponent 1/4−o(1) → computed threshold functions, two limits, two-sided gap constants, and for every η>0 an eventual lower bound k^((1/4−η)log₂k); reason: the quantified η formulation is equivalent to the stated lower exponent, with no loss in its leading constant
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Theorem 11.4, p. 53

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Model

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Theorem 11.4, p.53, including all threshold assertions of Theorem 1.5(2), p.7. -/
theorem theorem_11_4 :
  Filter.Tendsto epsOne Filter.atTop (nhds (1/2)) ∧
  Filter.Tendsto epsTwo Filter.atTop (nhds (1/2)) ∧
  (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ K₀ : ℕ, 2 ≤ K₀ ∧ ∀ k ≥ K₀,
    0 < epsOne k ∧ epsOne k < epsTwo k ∧ epsTwo k < 1/2 ∧
    epsTwo k - epsOne k = 1/(2*(L11 k : ℝ)^2) ∧
    c*(k : ℝ)^(-4 : ℝ) ≤ epsTwo k-epsOne k ∧
    epsTwo k-epsOne k ≤ C*(k : ℝ)^(-4 : ℝ)) ∧
  (∃ c : ℝ, 0 < c ∧ ∃ K₀ : ℕ, 2 ≤ K₀ ∧ ∀ k ≥ K₀,
    QLower (junta (n11 k) k) (epsOne k) (epsTwo k)
      (c * ((n11 k : ℝ)/(s11 k : ℝ))^((logceil k : ℝ)/4))) ∧
  (∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, 2 ≤ K₀ ∧ ∀ k ≥ K₀,
    QLower (junta (n11 k) k) (epsOne k) (epsTwo k)
      ((k : ℝ)^((1/4-η)*Real.logb 2 k))) := by sorry

end QTolTest1673.Unified.Supplement
