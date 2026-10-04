-- Prove2me | Theorems.Thm_TaoFivePrimes_eta1_deriv_L1
-- name    : TaoFivePrimes.eta1_deriv_L1
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T22:16:20.347872+00:00
-- url     : https://prove2.me/theorems/4619cb3b-1ca3-4109-a06f-fde56baea728
-- title:
--   Tao Section 8: $\|\eta_1'\|_{L^1(\mathbb{R})} = 2$
-- statement:
--   Throughout, $\eta_1$ is the symmetric trapezoidal cutoff of Section 8 of the source,
--
--   $$\eta_1(t)\;=\;\bigl(1-10\,\operatorname{dist}(t,[0.2,0.8])\bigr)_{+},$$
--
--   which is supported in $[0.1,0.9]$, equals $1$ on $[0.2,0.8]$, and rises and falls linearly with slope $\pm10$ in between.
--
--   The total variation of $\eta_1$ is $$\|\eta_1'\|_{L^1(\mathbb R)}=\int_{\mathbb R}|\eta_1'(t)|\,dt=2,$$ each of the two ramps contributing $1$.
--
--   The source records this together with the other norms of $\eta_1$ for repeated use in Section 8, where they are what is checked against the hypotheses of Corollary 4.9 and against the $L^2$ estimates of the final argument.
--
--   **Formalization Note** The derivative is the pointwise one, which exists off the four corners $0.1,0.2,0.8,0.9$; those points do not affect the integral.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 8, equation (8.6)

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory

theorem TaoFivePrimes.eta1_deriv_L1 :
    (∫ t : ℝ, |deriv TaoFivePrimes.eta1 t|) = 2 := by sorry
