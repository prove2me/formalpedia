-- Prove2me | Theorems.Thm_TaoFivePrimes_sum_sub_integral_le_half_deriv_L1
-- name    : TaoFivePrimes.sum_sub_integral_le_half_deriv_L1
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:56:23.423228+00:00
-- url     : https://prove2.me/theorems/48d35da9-6343-4163-8c14-da9fc186319c
-- title:
--   Tao Lemma 3.1 (3.1): the trapezoidal rule for a smooth compactly supported cutoff
-- statement:
--   Throughout, $F:\mathbb R\to\mathbb C$ is smooth and compactly supported and $e(t)=e^{2\pi i t}$.
--
--   The trapezoidal rule for the integer lattice:
--
--   $$\Bigl|\sum_{n\in\mathbb Z}F(n)-\int_{\mathbb R}F(y)\,dy\Bigr|\;\le\;\tfrac12\,\|F'\|_{L^1(\mathbb R)} .$$
--
--   In the source this is written $\sum_{n\in\mathbb Z}F(n)=\int_{\mathbb R}F+\mathcal O^{*}\bigl(\tfrac12\|F'\|_{L^1}\bigr)$, with $\mathcal O^{*}(E)$ a quantity of absolute value at most $E$.
--
--   This is the first of the three bounds of Lemma 3.1. It is what converts a discrete cutoff sum into its continuous counterpart with a controlled error, and in that form it supplies the denominator $\|\eta\|_{L^2}^2x+\|\eta\eta'\|_{L^1}$ of Proposition 4.8.
--
--   **Formalization Note** The bi-infinite sum is an unconditional sum over $\mathbb Z$, convergent because compact support leaves only finitely many nonzero terms.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 3, Lemma 3.1, equation (3.1)

import Mathlib

open MeasureTheory

theorem TaoFivePrimes.sum_sub_integral_le_half_deriv_L1
    (F : ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F) :
    ‖(∑' n : ℤ, F (n : ℝ)) - ∫ y : ℝ, F y‖ ≤ (1/2) * ∫ y : ℝ, ‖deriv F y‖ := by sorry
