-- Prove2me | Theorems.Thm_TaoFivePrimes_rh128_xi_approximation
-- name    : TaoFivePrimes.rh128_xi_approximation
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:13:43.735073+00:00
-- url     : https://prove2.me/theorems/ec1c80bb-9d11-4d05-8edb-c0dd92d02955
-- title:
--   Xi approximation on a radius-2.5 disk at height 128
-- statement:
--   Let $c=1/2+128i$, let $\xi$ be the completed Riemann xi function, and let $P$ be the stored local polynomial padded with zeros through degree 59. For $|z-c|\le5/2$,
--
--   $$
--   |10^{41}\xi(z)-P(z)|\le\frac{13}{100}.
--   $$
--
--   This disk estimate can be combined with exact polynomial inequalities to study zeros near height 128.
-- source:
--   Derived from the 336-moment enclosure and exact rational translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14
import Mathlib.Tactic

theorem TaoFivePrimes.rh128_xi_approximation (z : ℂ) (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center (256/2)‖ ≤ (5/2:ℝ)) :
    ‖((10^41:ℕ):ℂ)*RH1000Analytic.CertifiedLocalXi.xi z-
      TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH128RoundedCoefficients14 (10^14) 60 (256/2) z‖ ≤ 13/100 := by sorry
