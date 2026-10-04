-- Prove2me | Theorems.Thm_TaoFivePrimes_eta1_mul_deriv_L1
-- name    : TaoFivePrimes.eta1_mul_deriv_L1
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T22:16:25.093377+00:00
-- url     : https://prove2.me/theorems/1f5317bb-8d61-4a0a-bf9f-97342663a424
-- title:
--   Tao Section 8: $\|\eta_1\eta_1'\|_{L^1(\mathbb{R})} = 1$
-- statement:
--   Throughout, $\eta_1$ is the symmetric trapezoidal cutoff of Section 8 of the source,
--
--   $$\eta_1(t)\;=\;\bigl(1-10\,\operatorname{dist}(t,[0.2,0.8])\bigr)_{+},$$
--
--   which is supported in $[0.1,0.9]$, equals $1$ on $[0.2,0.8]$, and rises and falls linearly with slope $\pm10$ in between.
--
--   One has $$\|\eta_1\eta_1'\|_{L^1(\mathbb R)}=\int_{\mathbb R}\bigl|\eta_1(t)\,\eta_1'(t)\bigr|\,dt=1,$$ which is half the total variation of $\eta_1^2$.
--
--   The source records this together with the other norms of $\eta_1$ for repeated use in Section 8, where they are what is checked against the hypotheses of Corollary 4.9 and against the $L^2$ estimates of the final argument.
--
--   **Formalization Note** The derivative is the pointwise one, which exists off the four corners of $\eta_1$; those points do not affect the integral.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 8, equation (8.7)

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory

theorem TaoFivePrimes.eta1_mul_deriv_L1 :
    (∫ t : ℝ, |TaoFivePrimes.eta1 t * deriv TaoFivePrimes.eta1 t|) = 1 := by sorry
