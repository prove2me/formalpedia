-- Prove2me | Theorems.Thm_TaoFivePrimes_rh106p5_xi_approximation_wide
-- name    : TaoFivePrimes.rh106p5_xi_approximation_wide
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T18:05:06.548212+00:00
-- url     : https://prove2.me/theorems/3ebad5a1-7720-4bdb-ade4-2501b7e58704
-- title:
--   Certified xi approximation on the radius-1.6 disk centered at height 106.5
-- statement:
--   Let $\xi$ be the completed xi function, $c=\tfrac12+106.5i$, and $P$ the stored rounded local xi polynomial at that center. Then every complex $z$ in the disk $|z-c|\le8/5$ satisfies
--
--   $$
--   |10^{35}\xi(z)-P(z)|\le13.
--   $$
--
--   This wider-radius approximation extends the radius-one certificate and can be combined with exact polynomial bounds on rectangles beyond height $107$.
-- source:
--   Derived here from the proved Prove2Me TaoFivePrimes.rh14to100_moments_enclosed and TaoFivePrimes.rh106to107_translation_certificate using the local xi/Taylor framework of Prove2Me submission c64db120-69c7-4491-bac6-95122a310a7a. Existing moment and local method by sometik179, theta/Mellin foundations by Gabewhigham. The radius 8/5 and explicit error 13 are derived here. Related source: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH106To107RoundedCoefficients

theorem TaoFivePrimes.rh106p5_xi_approximation_wide (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center (213/2)‖ ≤ (8/5:ℝ)) :
    ‖((10^35:ℕ):ℂ)*RH1000Analytic.CertifiedLocalXi.xi z-
      TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH106To107RoundedCoefficients 40 (213/2) z‖ ≤ 13 := by sorry
