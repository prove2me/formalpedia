-- Prove2me | Theorems.Thm_TaoFivePrimes_zeta_zero_count_multiplicity_T0_le
-- name    : TaoFivePrimes.zeta_zero_count_multiplicity_T0_le
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-02T15:56:09.07684+00:00
-- url     : https://prove2.me/theorems/744bde09-66be-4acc-918e-2addd310f8f6
-- title:
--   Tao’s verified-height zeta zero count, with multiplicity
-- statement:
--   Set $T_0=3.29\times10^9$. Counting zeros of the Riemann zeta function with their orders of vanishing, the zero count in the closed strip satisfies
--
--   $$\sum_{\substack{\zeta(\rho)=0\\0\le\Re\rho\le1\\0\le\Im\rho\le T_0}}\operatorname{ord}_{\rho}\zeta\le10^{10}.$$
--
--   This is the numerical zero-count input stated immediately after Proposition 7.2 of Tao's paper. Multiplicity is essential for using it with the explicit formula and the corrected major-arc estimate. A bound on the number of distinct zeros alone does not imply this statement without an additional simplicity theorem.
--
--   **Formalization Note** The left side is a finite-sum expression using `analyticOrderNatAt` as the multiplicity. The estimate alone does not assert finiteness of the zero set; finiteness follows separately from the analytic properties of zeta. This node records the required count as an open proof obligation.
-- source:
--   T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section7, paragraph immediately following Proposition7.2 equations(7.3)–(7.4), printed p.34; the zero sum in its proof counts multiplicities. https://arxiv.org/html/1201.6656v4#S7

import Mathlib

theorem TaoFivePrimes.zeta_zero_count_multiplicity_T0_le :
    (∑ᶠ s ∈ {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ 3.29 * 10 ^ 9 ∧
        riemannZeta s = 0}, (analyticOrderNatAt riemannZeta s : ℝ)) ≤ (10 : ℝ) ^ 10 := by sorry
