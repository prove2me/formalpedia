-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0_L1_eq_one
-- name    : TaoFivePrimes.eta0_L1_eq_one
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:05:36.320127+00:00
-- url     : https://prove2.me/theorems/521027e9-4823-4b42-a3ce-d509b96f258b
-- title:
--   Tao equation (s1): the logarithmic cutoff $\eta_0$ has unit mass
-- statement:
--   Throughout, $\eta_0$ is the Lipschitz cutoff of unit mass supported in $[1/4,1]$ introduced in Section 1 of the source,
--
--   $$\eta_0(t)\;=\;4\bigl(\log 2-|\log 2t|\bigr)_{+},\qquad (u)_{+}=\max(0,u).$$
--
--   Its total mass is $$\|\eta_0\|_{L^1(\mathbb R)}=\int_{\mathbb R}\eta_0(t)\,dt=1.$$
--
--   The source records this together with the other norms of $\eta_0$ for repeated use in the minor-arc estimates of Sections 5 and 6, where each of them enters an explicit constant.
--
--   **Formalization Note** Since $\eta_0\ge0$, the $L^1$ norm is stated as the plain integral of $\eta_0$ over $\mathbb R$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5, equation (5.7)

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory

theorem TaoFivePrimes.eta0_L1_eq_one :
    (∫ t : ℝ, TaoFivePrimes.eta0 t) = 1 := by sorry
