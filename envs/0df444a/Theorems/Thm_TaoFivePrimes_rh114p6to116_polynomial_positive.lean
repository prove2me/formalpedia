-- Prove2me | Theorems.Thm_TaoFivePrimes_rh114p6to116_polynomial_positive
-- name    : TaoFivePrimes.rh114p6to116_polynomial_positive
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:55:12.951583+00:00
-- url     : https://prove2.me/theorems/29482c98-a11a-47e4-acf0-d5b2a0da8c92
-- title:
--   Polynomial positive certificate at heights 114.6–116
-- statement:
--   Let $P$ be the stored rounded local xi polynomial centered at $\tfrac12+114.5i$. For each $s=\sigma+it$ with $0\le\sigma\le1$ and $573/5\le t\le116$,
--
--   $$
--   \operatorname{Re}P(s)\ge5.
--   $$
--
--   This exact polynomial bound supports a finite-height zero-location argument when combined with a separate xi approximation.
-- source:
--   Derived from 304 scaled Mellin-moment enclosures and the exact height-114.5 translation. The xi/Taylor and bivariate Bernstein frameworks are due to sometik179 (Prove2Me submissions c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044); theta/Mellin foundations are due to Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH114p5RoundedCoefficients

theorem TaoFivePrimes.rh114p6to116_polynomial_positive (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (573/5:ℝ) ≤ s.im) (hb : s.im ≤ (116:ℝ)) :
    (5:ℝ) ≤ (TaoFivePrimes_RHLocalRoundedPolynomial
      TaoFivePrimes_RH114p5RoundedCoefficients 40 (229/2) s).re := by sorry
