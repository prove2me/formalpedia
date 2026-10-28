-- Prove2me | Theorems.Thm_TaoFivePrimes_rh114p5_xi_approximation
-- name    : TaoFivePrimes.rh114p5_xi_approximation
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:55:08.528743+00:00
-- url     : https://prove2.me/theorems/a64ae4c0-ba60-4424-ba1a-4c18f01a78ac
-- title:
--   Xi approximation on a radius-2.5 disk at height 114.5
-- statement:
--   Let $c=\tfrac12+114.5i$, let $\xi$ be the completed xi function, and let $P_{60}$ be the stored rounded local polynomial padded with zero coefficients. For every $|z-c|\le5/2$,
--
--   $$
--   |10^{37}\xi(z)-P_{60}(z)|\le\tfrac34.
--   $$
--
--   The disk estimate can be combined with exact polynomial bounds to locate zeros near height 114.5.
-- source:
--   Derived from 304 scaled Mellin-moment enclosures and the exact height-114.5 translation. The xi/Taylor and bivariate Bernstein frameworks are due to sometik179 (Prove2Me submissions c9908072-d99a-4431-aad8-a72c6352619a and f32249e2-6b1c-47ef-8195-015259f0d044); theta/Mellin foundations are due to Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH114p5RoundedCoefficients

theorem TaoFivePrimes.rh114p5_xi_approximation (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center (229/2)‖ ≤ (5/2:ℝ)) :
    ‖((10^37:ℕ):ℂ)*RH1000Analytic.CertifiedLocalXi.xi z-
      TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH114p5RoundedCoefficients 60 (229/2) z‖ ≤ 3/4 := by sorry
