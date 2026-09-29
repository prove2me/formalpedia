-- Prove2me | Theorems.Thm_TaoFivePrimes_two_norm_le_abs_sin_le_pi_norm
-- name    : TaoFivePrimes.two_norm_le_abs_sin_le_pi_norm
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:52:25.233447+00:00
-- url     : https://prove2.me/theorems/a072533c-84d0-4679-b543-8042cc2485b4
-- title:
--   Tao equation (2.1): comparison of $\|\alpha\|_{\mathbb{R}/\mathbb{Z}}$ with $|\sin\pi\alpha|$ and $|\tan\pi\alpha|$
-- statement:
--   For $\alpha\in\mathbb R$ write $\|\alpha\|_{\mathbb R/\mathbb Z}$ for the distance from $\alpha$ to the nearest integer. Then
--
--   $$2\,\|\alpha\|_{\mathbb R/\mathbb Z}\;\le\;\bigl|\sin(\pi\alpha)\bigr|\;\le\;\pi\,\|\alpha\|_{\mathbb R/\mathbb Z}\;\le\;\bigl|\tan(\pi\alpha)\bigr| ,$$
--
--   the last inequality under the additional assumption $\|\alpha\|_{\mathbb R/\mathbb Z}<\tfrac12$.
--
--   These are the elementary comparisons between the distance to the nearest integer and the trigonometric functions of $\pi\alpha$; they are used throughout the paper to pass between the two ways of measuring how close a frequency is to a rational with small denominator.
--
--   **Formalization Note** The distance to the nearest integer is written $|\alpha-\operatorname{round}\alpha|$. The last inequality is stated under the hypothesis $\|\alpha\|_{\mathbb R/\mathbb Z}<\tfrac12$ because at $\|\alpha\|_{\mathbb R/\mathbb Z}=\tfrac12$ the tangent is undefined; the source reads the right-hand side as $+\infty$ there.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 2, equation (2.1)

import Mathlib

theorem TaoFivePrimes.two_norm_le_abs_sin_le_pi_norm (alpha : ℝ) :
    2 * |alpha - round alpha| ≤ |Real.sin (Real.pi * alpha)|
      ∧ |Real.sin (Real.pi * alpha)| ≤ Real.pi * |alpha - round alpha|
      ∧ (|alpha - round alpha| < 1/2 →
          Real.pi * |alpha - round alpha| ≤ |Real.tan (Real.pi * alpha)|) := by sorry
