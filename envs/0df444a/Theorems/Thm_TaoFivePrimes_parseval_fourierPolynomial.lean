-- Prove2me | Theorems.Thm_TaoFivePrimes_parseval_fourierPolynomial
-- name    : TaoFivePrimes.parseval_fourierPolynomial
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T20:33:11.635258+00:00
-- url     : https://prove2.me/theorems/7658dd06-231f-4223-94fa-8dc7f109928b
-- title:
--   Plancherel's identity for a finite Fourier polynomial on the circle
-- statement:
--   Let $N\ge0$ and let $a_0,\dots,a_{N-1}$ be complex numbers. For the trigonometric polynomial
--
--   $$P(\alpha)\;=\;\sum_{0\le n<N}a_n\,e(\alpha n),\qquad e(t)=e^{2\pi i t},$$
--
--   one has
--
--   $$\int_{\mathbb R/\mathbb Z}\bigl|P(\alpha)\bigr|^{2}\,d\alpha\;=\;\sum_{0\le n<N}|a_n|^{2} .$$
--
--   This is the Plancherel identity for finite Fourier polynomials on the circle. It is the step by which the $L^2$ norm of a prime exponential sum is converted into a sum of squares of its coefficients, and in that form it is the starting point of Lemma 4.5 and of Proposition 4.10.
--
--   **Formalization Note** The circle is the additive circle $\mathbb R/\mathbb Z$ with its Haar probability measure, so no normalising factor appears.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, the Plancherel identity used in the proof of Lemma 4.5 (Global L^2 estimate)

import Mathlib
import Definitions.Def_TaoFivePrimes_FourierRepresentation

open MeasureTheory

theorem TaoFivePrimes.parseval_fourierPolynomial (N : ℕ) (a : ℕ → ℂ) :
    (∫ alpha : AddCircle (1 : ℝ),
        ‖TaoFourierIdentity.fourierPolynomial (Finset.range N) a (fun n => (n : ℤ)) alpha‖ ^ 2
        ∂AddCircle.haarAddCircle)
      = ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by sorry
