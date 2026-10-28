-- Prove2me | Theorems.Thm_TaoFivePrimes_rh130p8to131p15_imaginary_certificate
-- name    : TaoFivePrimes.rh130p8to131p15_imaginary_certificate
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:19:37.651756+00:00
-- url     : https://prove2.me/theorems/e449bd38-fd08-4ce1-8867-6bef70545d5d
-- title:
--   Imaginary polynomial bound at heights 130.8–131.15
-- statement:
--   Let $P$ be the stored rounded local polynomial centered at $1/2+128i$. For $s=\sigma+it$ with $0\le\sigma\le1$ and $130.8\le t\le131.15$,
--
--   $$
--   |\operatorname{Im}P(s)|\ge2|\sigma-1/2|.
--   $$
--
--   The exact polynomial inequality combines with a separate derivative estimate.
-- source:
--   Derived from the proved 336-moment enclosure and exact rational height-128 translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14
import Mathlib.Tactic

theorem TaoFivePrimes.rh130p8to131p15_imaginary_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (654/5:ℝ) ≤ s.im) (hb : s.im ≤ (2623/20:ℝ)) :
    (2:ℝ)*|s.re-1/2| ≤
      |(TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH128RoundedCoefficients14 (10^14)
        40 (256/2) s).im| := by sorry
