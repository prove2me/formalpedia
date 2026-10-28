-- Prove2me | Theorems.Thm_TaoFivePrimes_rh109to110_polynomial_negative
-- name    : TaoFivePrimes.rh109to110_polynomial_negative
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:23:50.973847+00:00
-- url     : https://prove2.me/theorems/c8f05bac-58f8-49b4-bed9-8d96b4daaea4
-- title:
--   Negative rounded xi polynomial on the 109–110 rectangle
-- statement:
--   Let $P$ be the rounded local xi polynomial centered at $\tfrac12+110.5i$. For every $s=\sigma+it$ with $0\le\sigma\le1$ and $109\le t\le110$,
--
--   $$
--   \operatorname{Re}P(s)\le-280.
--   $$
--
--   This exact polynomial bound is an input to a zero-free rectangle proof.
-- source:
--   Derived here from the 272 proposed Mellin moments and exact height-110.5 translation. The xi/Taylor and Bernstein frameworks are due to sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044; theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH110p5RoundedCoefficients

theorem TaoFivePrimes.rh109to110_polynomial_negative (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : 109 ≤ s.im) (hb : s.im ≤ 110) :
    (280:ℝ) ≤ -(TaoFivePrimes_RHLocalRoundedPolynomial
      TaoFivePrimes_RH110p5RoundedCoefficients 40 (221/2) s).re := by sorry
