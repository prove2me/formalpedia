-- Prove2me | Theorems.Thm_TaoFivePrimes_sum_odd_norm_le_half_L1_add_half_deriv_L1
-- name    : TaoFivePrimes.sum_odd_norm_le_half_L1_add_half_deriv_L1
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:30:22.598683+00:00
-- url     : https://prove2.me/theorems/bf5adc24-d4b4-431e-9d5b-2f7d9ee62e67
-- title:
--   Tao Corollary 3.2: restricting a smooth cutoff to the odd integers halves the $L^1$ term
-- statement:
--   Throughout, $F:\mathbb R\to\mathbb C$ is smooth and compactly supported and $e(t)=e^{2\pi i t}$.
--
--   Restricting the lattice to the odd integers halves the main term:
--
--   $$\sum_{m\in\mathbb Z}\bigl|F(2m+1)\bigr|\;\le\;\tfrac12\,\|F\|_{L^1(\mathbb R)}+\tfrac12\,\|F'\|_{L^1(\mathbb R)} .$$
--
--   Since $|e(\alpha(2m+1))|=1$, the same quantity bounds $\bigl|\sum_{m}F(2m+1)e(\alpha(2m+1))\bigr|$.
--
--   This is the first half of Corollary 3.2, the odd-restricted companion of Lemma 3.1. Restricting to odd integers is what lets the paper work with sums over odd primes and save a factor of two throughout Sections 5 and 6.
--
--   **Formalization Note** The bi-infinite sum is an unconditional sum over $\mathbb Z$, convergent because compact support leaves only finitely many nonzero terms.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 3, Corollary 3.2, first bound

import Mathlib

open MeasureTheory

theorem TaoFivePrimes.sum_odd_norm_le_half_L1_add_half_deriv_L1
    (F : ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F) :
    (∑' m : ℤ, ‖F (((2 * m + 1 : ℤ) : ℝ))‖)
      ≤ (1/2) * (∫ y : ℝ, ‖F y‖) + (1/2) * ∫ y : ℝ, ‖deriv F y‖ := by sorry
