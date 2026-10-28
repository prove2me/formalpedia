-- Prove2me | Theorems.Thm_TaoFivePrimes_rh128_xi_polynomial_derivative_bound_wide
-- name    : TaoFivePrimes.rh128_xi_polynomial_derivative_bound_wide
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:19:39.102822+00:00
-- url     : https://prove2.me/theorems/b04c5310-8709-493f-badd-498b47204a43
-- title:
--   Wider derivative bound for the height-128 xi approximation
-- statement:
--   Let $c=1/2+128i$ and $F(z)=10^{41}\xi(z)-P(z)$ for the stored local polynomial padded with zeros through degree 59. If $|z-c|\le16/5$, then
--
--   $$
--   |F'(z)|\le\frac74.
--   $$
--
--   This derivative estimate supports a separate critical-line zero-location argument.
-- source:
--   Derived from the proved 336-moment enclosure and exact rational height-128 translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14
import Mathlib.Tactic

theorem TaoFivePrimes.rh128_xi_polynomial_derivative_bound_wide (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center (256/2)‖ ≤ (16/5:ℝ)) :
    ‖deriv (fun w : ℂ => ((10^41:ℕ):ℂ)*RH1000Analytic.CertifiedLocalXi.xi w-
      TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH128RoundedCoefficients14
        (10^14) 60 (256/2) w) z‖ ≤ 7/4 := by sorry
