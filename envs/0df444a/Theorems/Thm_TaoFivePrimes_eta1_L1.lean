-- Prove2me | Theorems.Thm_TaoFivePrimes_eta1_L1
-- name    : TaoFivePrimes.eta1_L1
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T22:11:29.17079+00:00
-- url     : https://prove2.me/theorems/1a6a92d6-8708-45f5-bb4f-b521e3091b12
-- title:
--   Tao Section 8: $\|\eta_1\|_{L^1(\mathbb{R})} = 7/10$
-- statement:
--   Throughout, $\eta_1$ is the symmetric trapezoidal cutoff of Section 8 of the source,
--
--   $$\eta_1(t)\;=\;\bigl(1-10\,\operatorname{dist}(t,[0.2,0.8])\bigr)_{+},$$
--
--   which is supported in $[0.1,0.9]$, equals $1$ on $[0.2,0.8]$, and rises and falls linearly with slope $\pm10$ in between.
--
--   Its total mass is $$\|\eta_1\|_{L^1(\mathbb R)}=\int_{\mathbb R}\eta_1(t)\,dt=\frac7{10},$$ the plateau contributing $0.6$ and the two ramps $0.05$ each.
--
--   The source records this together with the other norms of $\eta_1$ for repeated use in Section 8, where they are what is checked against the hypotheses of Corollary 4.9 and against the $L^2$ estimates of the final argument.
--
--   **Formalization Note** Since $\eta_1\ge0$, the $L^1$ norm is stated as the plain integral.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 8, equation (8.4)

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory

theorem TaoFivePrimes.eta1_L1 : (∫ t : ℝ, TaoFivePrimes.eta1 t) = 7/10 := by sorry
