-- Prove2me | Theorems.Thm_TaoFivePrimes_rh130p4to130p8_polynomial_negative
-- name    : TaoFivePrimes.rh130p4to130p8_polynomial_negative
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:19:37.598691+00:00
-- url     : https://prove2.me/theorems/2b158d00-ad11-4596-bee3-4bd1c649120d
-- title:
--   Negative polynomial bound at heights 130.4–130.8
-- statement:
--   Let $P$ be the stored rounded local polynomial centered at $1/2+128i$. For $s=\sigma+it$ with $0\le\sigma\le1$ and $130.4\le t\le130.8$,
--
--   $$
--   -\operatorname{Re}P(s)\ge\frac7{10}.
--   $$
--
--   The exact polynomial inequality is separate from the xi approximation.
-- source:
--   Derived from the proved 336-moment enclosure and exact rational height-128 translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14
import Mathlib.Tactic

theorem TaoFivePrimes.rh130p4to130p8_polynomial_negative (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (652/5:ℝ) ≤ s.im) (hb : s.im ≤ (654/5:ℝ)) :
    ((7/10):ℝ) ≤ -(TaoFivePrimes_RHLocalRationalPolynomial
      TaoFivePrimes_RH128RoundedCoefficients14 (10^14) 40 (256/2) s).re := by sorry
