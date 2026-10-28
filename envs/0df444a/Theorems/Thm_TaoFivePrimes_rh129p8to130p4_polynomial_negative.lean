-- Prove2me | Theorems.Thm_TaoFivePrimes_rh129p8to130p4_polynomial_negative
-- name    : TaoFivePrimes.rh129p8to130p4_polynomial_negative
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:13:44.307007+00:00
-- url     : https://prove2.me/theorems/c5eeb831-4ff5-4c39-9cac-1149d729c39b
-- title:
--   Negative polynomial bound at heights 129.8–130.4
-- statement:
--   Let $P$ be the stored rounded local polynomial centered at $1/2+128i$. For $s=\sigma+it$ with $0\le\sigma\le1$ and $129.8\le t\le130.4$,
--
--   $$
--   -\operatorname{Re}P(s)\ge 1.
--   $$
--
--   This exact polynomial inequality is separate from the analytic approximation.
-- source:
--   Derived from the 336-moment enclosure and exact rational translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14
import Mathlib.Tactic

theorem TaoFivePrimes.rh129p8to130p4_polynomial_negative (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (649/5:ℝ) ≤ s.im) (hb : s.im ≤ (652/5:ℝ)) :
    (1:ℝ) ≤ -(TaoFivePrimes_RHLocalRationalPolynomial
      TaoFivePrimes_RH128RoundedCoefficients14 (10^14) 40 (256/2) s).re := by sorry
