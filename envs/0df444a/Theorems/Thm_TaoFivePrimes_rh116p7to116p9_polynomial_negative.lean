-- Prove2me | Theorems.Thm_TaoFivePrimes_rh116p7to116p9_polynomial_negative
-- name    : TaoFivePrimes.rh116p7to116p9_polynomial_negative
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:55:17.05823+00:00
-- url     : https://prove2.me/theorems/f80ffee2-acf0-402f-9eca-39d8e9b24986
-- title:
--   Polynomial negative certificate at heights 116.7–116.9
-- statement:
--   Let $P$ be the stored rounded local xi polynomial centered at $\tfrac12+114.5i$. For each $s=\sigma+it$ with $0\le\sigma\le1$ and $1167/10\le t\le1169/10$,
--
--   $$
--   \operatorname{Re}P(s)\le-11.
--   $$
--
--   This exact polynomial bound supports a finite-height zero-location argument when combined with a separate xi approximation.
-- source:
--   Derived from 304 scaled Mellin-moment enclosures and the exact height-114.5 translation. The xi/Taylor and bivariate Bernstein frameworks are due to sometik179 (Prove2Me submissions c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044); theta/Mellin foundations are due to Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH114p5RoundedCoefficients

theorem TaoFivePrimes.rh116p7to116p9_polynomial_negative (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (1167/10:ℝ) ≤ s.im) (hb : s.im ≤ (1169/10:ℝ)) :
    (11:ℝ) ≤ -(TaoFivePrimes_RHLocalRoundedPolynomial
      TaoFivePrimes_RH114p5RoundedCoefficients 40 (229/2) s).re := by sorry
