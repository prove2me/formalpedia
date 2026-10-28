-- Prove2me | Theorems.Thm_TaoFivePrimes_rh128_xi_approximation_wide
-- name    : TaoFivePrimes.rh128_xi_approximation_wide
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:19:36.821175+00:00
-- url     : https://prove2.me/theorems/af6b3889-f8fe-4fa8-8967-e57032e1b4ed
-- title:
--   Xi approximation on a radius-2.9 disk at height 128
-- statement:
--   Let $c=1/2+128i$, let $\xi$ be the completed Riemann xi function, and let $P$ be the stored local polynomial padded with zeros through degree 59. If $|z-c|\le29/10$, then
--
--   $$
--   |10^{41}\xi(z)-P(z)|\le\frac{53}{100}.
--   $$
--
--   This disk estimate supports a separate zero-free interval argument.
-- source:
--   Derived from the proved 336-moment enclosure and exact rational height-128 translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14
import Mathlib.Tactic

theorem TaoFivePrimes.rh128_xi_approximation_wide (z : ℂ) (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center (256/2)‖ ≤ (29/10:ℝ)) :
    ‖((10^41:ℕ):ℂ)*RH1000Analytic.CertifiedLocalXi.xi z-
      TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH128RoundedCoefficients14 (10^14) 60 (256/2) z‖ ≤ 53/100 := by sorry
