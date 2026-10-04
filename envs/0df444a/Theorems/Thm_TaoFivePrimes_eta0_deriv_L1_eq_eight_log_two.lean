-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0_deriv_L1_eq_eight_log_two
-- name    : TaoFivePrimes.eta0_deriv_L1_eq_eight_log_two
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:14:06.443192+00:00
-- url     : https://prove2.me/theorems/81a401be-7276-4bf0-b911-68a27143a47d
-- title:
--   Tao equation (s1-3): the $L^1$ norm of $\eta_0'$ is $8\log 2$
-- statement:
--   Throughout, $\eta_0$ is the Lipschitz cutoff of unit mass supported in $[1/4,1]$ introduced in Section 1 of the source,
--
--   $$\eta_0(t)\;=\;4\bigl(\log 2-|\log 2t|\bigr)_{+},\qquad (u)_{+}=\max(0,u).$$
--
--   The total variation of $\eta_0$ is $$\|\eta_0'\|_{L^1(\mathbb R)}=\int_{\mathbb R}|\eta_0'(t)|\,dt=8\log 2.$$
--
--   The source records this together with the other norms of $\eta_0$ for repeated use in the minor-arc estimates of Sections 5 and 6, where each of them enters an explicit constant.
--
--   **Formalization Note** $\eta_0$ is only piecewise smooth, with corners at $t=1/4$, $t=1/2$ and $t=1$; the derivative is the pointwise one, which exists off that finite set, and the three exceptional points do not affect the integral.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, equation (5.9)

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory

theorem TaoFivePrimes.eta0_deriv_L1_eq_eight_log_two :
    (∫ t : ℝ, |deriv TaoFivePrimes.eta0 t|) = 8 * Real.log 2 := by sorry
