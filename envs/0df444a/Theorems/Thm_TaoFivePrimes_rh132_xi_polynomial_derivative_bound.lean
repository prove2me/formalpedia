-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_xi_polynomial_derivative_bound
-- name    : TaoFivePrimes.rh132_xi_polynomial_derivative_bound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T01:00:00.858328+00:00
-- url     : https://prove2.me/theorems/fdbbf536-0dd5-4279-b90c-2b355c663240
-- title:
--   Xi approximation derivative bound near height 132
-- statement:
--   Let $c=1/2+132i$ and let $F(z)=10^{43}\xi(z)-P(z)$, where $P$ is the stored local polynomial. For every $z$ with $|z-c|\le61/20$,
--
--   $$
--   |F'(z)|\le\frac{27}{50}.
--   $$
--
--   This derivative estimate supports separate critical-line zero-location arguments.
-- source:
--   Cauchy estimate using the local xi approximation built on the theta/Mellin framework of Gabewhigham and sometik179.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH132RoundedCoefficients14
import Mathlib

theorem TaoFivePrimes.rh132_xi_polynomial_derivative_bound (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center 132‖≤(61/20:ℝ)) :
    ‖deriv (fun w : ℂ => (10^43:ℂ)*RH1000Analytic.CertifiedLocalXi.xi w -
      TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
        (10^14) 60 132 w) z‖≤27/50 := by sorry
