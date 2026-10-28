-- Prove2me | Theorems.Thm_TaoFivePrimes_rh129p3to129p8_imaginary_certificate
-- name    : TaoFivePrimes.rh129p3to129p8_imaginary_certificate
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:13:42.159191+00:00
-- url     : https://prove2.me/theorems/22e487df-37f2-4133-81d8-2cf12c295f6d
-- title:
--   Imaginary polynomial bound at heights 129.3–129.8
-- statement:
--   Let $P$ be the stored rounded local polynomial centered at $1/2+128i$. For $s=\sigma+it$ with $0\le\sigma\le1$ and $129.3\le t\le129.8$,
--
--   $$
--   |\operatorname{Im}P(s)|\ge 3|\sigma-1/2|.
--   $$
--
--   This exact polynomial inequality is separate from the analytic approximation.
-- source:
--   Derived from the 336-moment enclosure and exact rational translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14
import Mathlib.Tactic

theorem TaoFivePrimes.rh129p3to129p8_imaginary_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (1293/10:ℝ) ≤ s.im) (hb : s.im ≤ (649/5:ℝ)) :
    (3:ℝ)*|s.re-1/2| ≤
      |(TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH128RoundedCoefficients14 (10^14)
        40 (256/2) s).im| := by sorry
