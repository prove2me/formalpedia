-- Prove2me | Theorems.Thm_TaoFivePrimes_rh111p25to111p7_polynomial_positive
-- name    : TaoFivePrimes.rh111p25to111p7_polynomial_positive
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:24:04.011526+00:00
-- url     : https://prove2.me/theorems/d47049c9-5363-4442-819c-14523fa95d0a
-- title:
--   Positive rounded xi polynomial on the 111.25–111.7 rectangle
-- statement:
--   Let $P$ be the rounded local xi polynomial centered at $\tfrac12+110.5i$. For every $s=\sigma+it$ with $0\le\sigma\le1$ and $111.25\le t\le111.7$,
--
--   $$
--   \operatorname{Re}P(s)\ge6.
--   $$
--
--   This exact polynomial bound is an input to a zero-free rectangle proof.
-- source:
--   Derived here from the 272 proposed Mellin moments and exact height-110.5 translation. The xi/Taylor and Bernstein frameworks are due to sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044; theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH110p5RoundedCoefficients

theorem TaoFivePrimes.rh111p25to111p7_polynomial_positive (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (445/4:ℝ) ≤ s.im) (hb : s.im ≤ (1117/10:ℝ)) :
    (6:ℝ) ≤ (TaoFivePrimes_RHLocalRoundedPolynomial
      TaoFivePrimes_RH110p5RoundedCoefficients 40 (221/2) s).re := by sorry
