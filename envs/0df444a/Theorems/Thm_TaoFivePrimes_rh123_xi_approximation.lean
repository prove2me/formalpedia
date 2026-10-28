-- Prove2me | Theorems.Thm_TaoFivePrimes_rh123_xi_approximation
-- name    : TaoFivePrimes.rh123_xi_approximation
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:36:05.512445+00:00
-- url     : https://prove2.me/theorems/2e52271d-c0cc-4d60-907f-3f6b6d3a286a
-- title:
--   Xi approximation on a radius-2.5 disk at height 123
-- statement:
--   Let $c=1/2+123i$, let $\xi$ be the completed Riemann xi function, and let $P_{60}$ be the stored rounded local polynomial, padded with zero coefficients through degree 59. For every $|z-c|\le5/2$,
--
--   $$
--   |10^{40}\xi(z)-P_{60}(z)|\le\frac7{1000}.
--   $$
--
--   The estimate can be combined with exact polynomial inequalities to study zeros near height 123.
-- source:
--   Adapted from the proved height-119 xi approximation and the theta/Mellin framework due to sometik179 and Gabewhigham. The 320-moment and height-123 translation bounds are separate dependencies.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH123RoundedCoefficients12
import Mathlib.Tactic

theorem TaoFivePrimes.rh123_xi_approximation (z : ℂ) (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center (246/2)‖ ≤ (5/2:ℝ)) :
    ‖((10^40:ℕ):ℂ)*RH1000Analytic.CertifiedLocalXi.xi z-
      TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH123RoundedCoefficients12 (10^12) 60 (246/2) z‖ ≤ 7/1000 := by sorry
