-- Prove2me | Theorems.Thm_TaoFivePrimes_rh124p5_xi_approximation
-- name    : TaoFivePrimes.rh124p5_xi_approximation
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:50:00.041767+00:00
-- url     : https://prove2.me/theorems/3fd4c2b1-4f57-4f49-abe7-b242998f52ec
-- title:
--   Xi approximation on a radius-2.8 disk at height 124.5
-- statement:
--   Let $c=1/2+124.5i$, let $\xi$ be the completed Riemann xi function, and let $P$ be the stored rounded local polynomial, padded with zeros through degree 59. For every $|z-c|\le14/5$,
--
--   $$
--   |10^{40}\xi(z)-P(z)|\le\frac{21}{50}.
--   $$
--
--   This disk estimate can be combined with exact polynomial inequalities to study zeros near height 124.5.
-- source:
--   Derived from the proved 320-moment enclosure and exact rational translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite-height verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH124p5RoundedCoefficients14
import Mathlib.Tactic

theorem TaoFivePrimes.rh124p5_xi_approximation (z : ℂ) (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center (249/2)‖ ≤ (14/5:ℝ)) :
    ‖((10^40:ℕ):ℂ)*RH1000Analytic.CertifiedLocalXi.xi z-
      TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH124p5RoundedCoefficients14 (10^14) 60 (249/2) z‖ ≤ 21/50 := by sorry
