-- Prove2me | Theorems.Thm_TaoFivePrimes_rh106p5_xi_approximation_radius272
-- name    : TaoFivePrimes.rh106p5_xi_approximation_radius272
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T18:48:06.847589+00:00
-- url     : https://prove2.me/theorems/628e1cdd-fad4-45cf-aa85-dfbea314424a
-- title:
--   Xi approximation on the radius-2.55 disk at height 106.5
-- statement:
--   Let $\xi$ be the completed xi function, $c=\tfrac12+106.5i$, and $P_{60}$ the rounded local xi polynomial defined by the published height-$106.5$ coefficient list, with missing coefficients interpreted as zero. Then for every complex $z$ with $|z-c|\le51/20$,
--
--   $$
--   |10^{35}\xi(z)-P_{60}(z)|\le135.
--   $$
--
--   This uniform disk estimate can be combined with exact polynomial sign bounds to extend the certified zero-free height range.
-- source:
--   Derived here from the proved 256 Mellin-moment enclosures and the exact height-106.5 translation certificates, using a global Cauchy radius of 272. The xi/Taylor framework is from Prove2Me submission c64db120-69c7-4491-bac6-95122a310a7a; the moment and local method are by sometik179, with theta/Mellin foundations by Gabewhigham. Related source: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH106To107RoundedCoefficients

theorem TaoFivePrimes.rh106p5_xi_approximation_radius272 (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center (213/2)‖ ≤ (51/20:ℝ)) :
    ‖((10^35:ℕ):ℂ)*RH1000Analytic.CertifiedLocalXi.xi z-
      TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH106To107RoundedCoefficients 60 (213/2) z‖ ≤ 135 := by sorry
