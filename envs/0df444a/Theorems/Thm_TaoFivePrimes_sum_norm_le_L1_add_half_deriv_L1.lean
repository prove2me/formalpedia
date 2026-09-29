-- Prove2me | Theorems.Thm_TaoFivePrimes_sum_norm_le_L1_add_half_deriv_L1
-- name    : TaoFivePrimes.sum_norm_le_L1_add_half_deriv_L1
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:20:17.641968+00:00
-- url     : https://prove2.me/theorems/37adeb8f-4250-4f17-82e7-a21128f4237d
-- title:
--   Tao Lemma 3.1: a smooth cutoff sampled at the integers is bounded by its $L^1$ norms
-- statement:
--   Throughout, $F:\mathbb R\to\mathbb C$ is smooth and compactly supported and $e(t)=e^{2\pi i t}$.
--
--   The $\ell^1$ form of the trapezoidal rule:
--
--   $$\sum_{n\in\mathbb Z}\bigl|F(n)\bigr|\;\le\;\|F\|_{L^1(\mathbb R)}+\tfrac12\,\|F'\|_{L^1(\mathbb R)} .$$
--
--   Since $|e(\alpha n)|=1$, this immediately bounds $\bigl|\sum_{n}F(n)e(\alpha n)\bigr|$ by the same quantity, which is the form in which the source states it.
--
--   This is the second of the three bounds of Lemma 3.1; it is the estimate used when no cancellation in the exponential is available, in particular for frequencies close to the origin.
--
--   **Formalization Note** The bi-infinite sum is an unconditional sum over $\mathbb Z$, convergent because compact support leaves only finitely many nonzero terms.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 3, Lemma 3.1, equation (3.2)

import Mathlib

open MeasureTheory

theorem TaoFivePrimes.sum_norm_le_L1_add_half_deriv_L1
    (F : ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F) :
    (∑' n : ℤ, ‖F (n : ℝ)‖)
      ≤ (∫ y : ℝ, ‖F y‖) + (1/2) * ∫ y : ℝ, ‖deriv F y‖ := by sorry
