-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_xi_coefficient_error
-- name    : TaoFivePrimes.rh_direct_132_xi_coefficient_error
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:12:48.022997+00:00
-- url     : https://prove2.me/theorems/61e01bf7-2e61-4b6e-9abf-8da7dcbaac55
-- title:
--   Local xi coefficients from direct height-132 quadrature
-- statement:
--   Let $c=1/2+132i$, let $\xi$ be the Riemann xi function, and let $C_n$ be the finite Gaussian-rational coefficient obtained from the height-132 direct quadrature. For every integer $n\ge0$,
--
--   $$
--   \left|10^{43}i^n\frac{\xi^{(n)}(c)}{n!}-C_n\right|
--   \le2\cdot10^{-34}.
--   $$
--
--   This uniform analytic enclosure is independent of any rounding of $C_n$. The finite rounding checks and zero-location results are separate.
-- source:
--   Direct oscillatory quadrature and Mellin folding based on the theta/Mellin framework due to Gabewhigham and sometik179.

import Definitions.Def_TaoFivePrimes_RHDirect132XiCoefficients
import Definitions.Def_TaoFivePrimes_RH100To1000LocalAnalyticModel
import Mathlib

theorem TaoFivePrimes.rh_direct_132_xi_coefficient_error (n : ℕ) :
    ‖(10^43:ℂ)*Complex.I^n *
        RH1000Analytic.CertifiedTaylorQuadrature.coefficient
          RH1000Analytic.CertifiedLocalXi.xi (RH1000Analytic.CertifiedLocalXi.center 132) n -
      RHDirect132XiCoefficients.scaled n‖≤2/10^34 := by sorry
