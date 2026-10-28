-- Prove2me | Theorems.Thm_TaoFivePrimes_rh110p5_xi_approximation_wide
-- name    : TaoFivePrimes.rh110p5_xi_approximation_wide
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:33:48.103376+00:00
-- url     : https://prove2.me/theorems/acbe3788-00d6-4257-8dd2-cdf47f68c894
-- title:
--   Xi approximation on a radius-2.5 disk at height 110.5
-- statement:
--   Let $c=\tfrac12+110.5i$, let $\xi$ be the completed xi function, and let $P_{60}$ be the stored rounded local polynomial padded with zero coefficients. For every $|z-c|\le5/2$,
--
--   $$
--   |10^{36}\xi(z)-P_{60}(z)|\le\tfrac9{10}.
--   $$
--
--   This disk estimate supplies a reusable analytic input for finite zero-location certificates near height 110.5.
-- source:
--   Derived from the 272 proved Mellin-moment bounds and exact height-110.5 translation. The xi/Taylor and Bernstein frameworks are due to sometik179, Prove2Me submissions c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044; theta/Mellin foundations are due to Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH110p5RoundedCoefficients

theorem TaoFivePrimes.rh110p5_xi_approximation_wide (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center (221/2)‖ ≤ (5/2:ℝ)) :
    ‖((10^36:ℕ):ℂ)*RH1000Analytic.CertifiedLocalXi.xi z-
      TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH110p5RoundedCoefficients 60 (221/2) z‖ ≤ 9/10 := by sorry
