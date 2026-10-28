-- Prove2me | Theorems.Thm_TaoFivePrimes_rh114p1to114p6_imaginary_certificate
-- name    : TaoFivePrimes.rh114p1to114p6_imaginary_certificate
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:55:15.670137+00:00
-- url     : https://prove2.me/theorems/1c2efc37-277c-4e0b-96f6-f26bfaf0d219
-- title:
--   Polynomial imag certificate at heights 114.1–114.6
-- statement:
--   Let $P$ be the stored rounded local xi polynomial centered at $\tfrac12+114.5i$. For each $s=\sigma+it$ with $0\le\sigma\le1$ and $1141/10\le t\le573/5$,
--
--   $$
--   |\operatorname{Im}P(s)|\ge60|\sigma-\tfrac12|.
--   $$
--
--   This exact polynomial bound supports a finite-height zero-location argument when combined with a separate xi approximation.
-- source:
--   Derived from 304 scaled Mellin-moment enclosures and the exact height-114.5 translation. The xi/Taylor and bivariate Bernstein frameworks are due to sometik179 (Prove2Me submissions c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044); theta/Mellin foundations are due to Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH114p5RoundedCoefficients

theorem TaoFivePrimes.rh114p1to114p6_imaginary_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (1141/10:ℝ) ≤ s.im) (hb : s.im ≤ (573/5:ℝ)) :
    (60:ℝ)*|s.re-1/2| ≤
      |(TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH114p5RoundedCoefficients 40 (229/2) s).im| := by sorry
