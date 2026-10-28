-- Prove2me | Theorems.Thm_TaoFivePrimes_rh112p1to112p9_polynomial_negative
-- name    : TaoFivePrimes.rh112p1to112p9_polynomial_negative
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:33:51.231985+00:00
-- url     : https://prove2.me/theorems/633d1019-df1a-494e-b16b-20fbc3cc63da
-- title:
--   Negative rounded xi polynomial on the 112.1–112.9 rectangle
-- statement:
--   Let $P$ be the rounded local xi polynomial centered at $\tfrac12+110.5i$. For every $s=\sigma+it$ with $0\le\sigma\le1$ and $112.1\le t\le112.9$,
--
--   $$
--   \operatorname{Re}P(s)\le-8.
--   $$
--
--   This exact sign bound can be combined with an xi approximation to exclude zeros in this part of the critical strip.
-- source:
--   Derived from the 272 proved Mellin-moment bounds and exact height-110.5 translation. The xi/Taylor and Bernstein frameworks are due to sometik179, Prove2Me submissions c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044; theta/Mellin foundations are due to Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH110p5RoundedCoefficients

theorem TaoFivePrimes.rh112p1to112p9_polynomial_negative (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (1121/10:ℝ) ≤ s.im) (hb : s.im ≤ (1129/10:ℝ)) :
    (8:ℝ) ≤ -(TaoFivePrimes_RHLocalRoundedPolynomial
      TaoFivePrimes_RH110p5RoundedCoefficients 40 (221/2) s).re := by sorry
