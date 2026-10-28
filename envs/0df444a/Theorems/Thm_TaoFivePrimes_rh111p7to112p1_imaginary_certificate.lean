-- Prove2me | Theorems.Thm_TaoFivePrimes_rh111p7to112p1_imaginary_certificate
-- name    : TaoFivePrimes.rh111p7to112p1_imaginary_certificate
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:33:51.646327+00:00
-- url     : https://prove2.me/theorems/ce5fb57a-53a0-46d5-82bb-eff5acf58f9b
-- title:
--   Imaginary-part margin on the 111.7–112.1 rectangle
-- statement:
--   Let $P$ be the rounded local xi polynomial centered at $\tfrac12+110.5i$. For every $s=\sigma+it$ with $0\le\sigma\le1$ and $111.7\le t\le112.1$,
--
--   $$
--   |\operatorname{Im}P(s)|\ge30|\sigma-\tfrac12|.
--   $$
--
--   This exact polynomial bound can be combined with an approximation error derivative bound to locate any zeros in the slice.
-- source:
--   Derived from the 272 proved Mellin-moment bounds and exact height-110.5 translation. The xi/Taylor and Bernstein frameworks are due to sometik179, Prove2Me submissions c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044; theta/Mellin foundations are due to Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH110p5RoundedCoefficients

theorem TaoFivePrimes.rh111p7to112p1_imaginary_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (1117/10:ℝ) ≤ s.im) (hb : s.im ≤ (1121/10:ℝ)) :
    (30:ℝ)*|s.re-1/2| ≤
      |(TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH110p5RoundedCoefficients 40 (221/2) s).im| := by sorry
