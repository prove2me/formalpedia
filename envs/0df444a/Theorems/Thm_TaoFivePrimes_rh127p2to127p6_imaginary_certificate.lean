-- Prove2me | Theorems.Thm_TaoFivePrimes_rh127p2to127p6_imaginary_certificate
-- name    : TaoFivePrimes.rh127p2to127p6_imaginary_certificate
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:56:21.623177+00:00
-- url     : https://prove2.me/theorems/2a357d5b-e5e7-4bd9-8413-48aff34c2977
-- title:
--   Imaginary polynomial bound at heights 127.2–127.6
-- statement:
--   Let $P$ be the stored rounded local polynomial centered at $1/2+124.5i$. For $s=\sigma+it$ with $0\le\sigma\le1$ and $127.2\le t\le127.6$,
--
--   $$
--   |\operatorname{Im}P(s)|\ge5|\sigma-1/2|.
--   $$
--
--   This exact polynomial inequality combines with a separate derivative bound for the xi approximation.
-- source:
--   Derived from the proved 320-moment enclosure and exact rational translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite-height verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH124p5RoundedCoefficients14
import Mathlib.Tactic

theorem TaoFivePrimes.rh127p2to127p6_imaginary_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (636/5:ℝ) ≤ s.im) (hb : s.im ≤ (638/5:ℝ)) :
    (5:ℝ)*|s.re-1/2| ≤
      |(TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH124p5RoundedCoefficients14 (10^14)
        40 (249/2) s).im| := by sorry
