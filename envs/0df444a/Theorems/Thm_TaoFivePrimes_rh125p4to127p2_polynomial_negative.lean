-- Prove2me | Theorems.Thm_TaoFivePrimes_rh125p4to127p2_polynomial_negative
-- name    : TaoFivePrimes.rh125p4to127p2_polynomial_negative
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:50:00.538984+00:00
-- url     : https://prove2.me/theorems/0e022aa8-56ab-41a5-9113-67e680b66978
-- title:
--   Negative polynomial bound at heights 125.4–127.2
-- statement:
--   Let $P$ be the stored rounded local polynomial centered at $1/2+124.5i$. For $s=\sigma+it$ with $0\le\sigma\le1$ and $125.4\le t\le127.2$,
--
--   $$
--   -\operatorname{Re}P(s)\ge\frac34.
--   $$
--
--   This is an exact polynomial inequality; the analytic approximation to $\xi$ is separate.
-- source:
--   Derived from the proved 320-moment enclosure and exact rational translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite-height verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH124p5RoundedCoefficients14
import Mathlib.Tactic

theorem TaoFivePrimes.rh125p4to127p2_polynomial_negative (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (627/5:ℝ) ≤ s.im) (hb : s.im ≤ (636/5:ℝ)) :
    ((3/4):ℝ) ≤ -(TaoFivePrimes_RHLocalRationalPolynomial
      TaoFivePrimes_RH124p5RoundedCoefficients14 (10^14) 40 (249/2) s).re := by sorry
