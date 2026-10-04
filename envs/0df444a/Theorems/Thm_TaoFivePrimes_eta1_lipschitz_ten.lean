-- Prove2me | Theorems.Thm_TaoFivePrimes_eta1_lipschitz_ten
-- name    : TaoFivePrimes.eta1_lipschitz_ten
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T22:11:37.409101+00:00
-- url     : https://prove2.me/theorems/8d40c52f-6652-4b2e-b643-e605d158ce61
-- title:
--   Tao Section 8: $\|\eta_1'\|_{L^\infty(\mathbb{R})} = 10$
-- statement:
--   Throughout, $\eta_1$ is the symmetric trapezoidal cutoff of Section 8 of the source,
--
--   $$\eta_1(t)\;=\;\bigl(1-10\,\operatorname{dist}(t,[0.2,0.8])\bigr)_{+},$$
--
--   which is supported in $[0.1,0.9]$, equals $1$ on $[0.2,0.8]$, and rises and falls linearly with slope $\pm10$ in between.
--
--   It is Lipschitz with constant $$\|\eta_1'\|_{L^\infty(\mathbb R)}=10,$$ that is, $|\eta_1(s)-\eta_1(t)|\le 10|s-t|$ for all real $s,t$.
--
--   The source records this together with the other norms of $\eta_1$ for repeated use in Section 8, where they are what is checked against the hypotheses of Corollary 4.9 and against the $L^2$ estimates of the final argument.
--
--   **Formalization Note** Because $\eta_1$ has corners at $0.1,0.2,0.8,0.9$, the sup-norm of its derivative is stated in the equivalent form of a Lipschitz bound with constant $10$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 8, equation (8.5)

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory

theorem TaoFivePrimes.eta1_lipschitz_ten : LipschitzWith 10 TaoFivePrimes.eta1 := by sorry
