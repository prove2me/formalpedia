-- Prove2me | Theorems.Thm_TaoFivePrimes_rh110to111p25_imaginary_certificate
-- name    : TaoFivePrimes.rh110to111p25_imaginary_certificate
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:23:49.825993+00:00
-- url     : https://prove2.me/theorems/f9535b93-6c6e-431a-823a-ddbfb56fce0f
-- title:
--   Imaginary-part margin for the height 110–111.25 polynomial
-- statement:
--   Let $P$ be the rounded local xi polynomial centered at $\tfrac12+110.5i$. Throughout $0\le\sigma\le1$ and $110\le t\le111.25$,
--
--   $$
--   |\operatorname{Im}P(\sigma+it)|\ge3|\sigma-\tfrac12|.
--   $$
--
--   This exact bound can be combined with a derivative bound for the approximation error to locate any zeros in the slice.
-- source:
--   Derived here from the 272 proposed Mellin moments and exact height-110.5 translation. The xi/Taylor and Bernstein frameworks are due to sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044; theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH110p5RoundedCoefficients

theorem TaoFivePrimes.rh110to111p25_imaginary_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : 110 ≤ s.im) (hb : s.im ≤ (445/4:ℝ)) :
    (3:ℝ)*|s.re-1/2| ≤
      |(TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH110p5RoundedCoefficients 40 (221/2) s).im| := by sorry
