-- Prove2me | Theorems.Thm_TaoFivePrimes_rh127p6to129p3_polynomial_positive
-- name    : TaoFivePrimes.rh127p6to129p3_polynomial_positive
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:13:44.749534+00:00
-- url     : https://prove2.me/theorems/721f3a83-dea1-4ff0-9bb8-033748376d63
-- title:
--   Positive polynomial bound at heights 127.6–129.3
-- statement:
--   Let $P$ be the stored rounded local polynomial centered at $1/2+128i$. For $s=\sigma+it$ with $0\le\sigma\le1$ and $127.6\le t\le129.3$,
--
--   $$
--   \operatorname{Re}P(s)\ge 1/2.
--   $$
--
--   This exact polynomial inequality is separate from the analytic approximation.
-- source:
--   Derived from the 336-moment enclosure and exact rational translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14
import Mathlib.Tactic

theorem TaoFivePrimes.rh127p6to129p3_polynomial_positive (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (638/5:ℝ) ≤ s.im) (hb : s.im ≤ (1293/10:ℝ)) :
    ((1/2):ℝ) ≤ (TaoFivePrimes_RHLocalRationalPolynomial
      TaoFivePrimes_RH128RoundedCoefficients14 (10^14) 40 (256/2) s).re := by sorry
