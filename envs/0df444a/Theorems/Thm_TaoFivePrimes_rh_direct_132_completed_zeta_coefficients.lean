-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_completed_zeta_coefficients
-- name    : TaoFivePrimes.rh_direct_132_completed_zeta_coefficients
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:59:33.541989+00:00
-- url     : https://prove2.me/theorems/de27aa74-b57b-41c1-9f07-988886cc97df
-- title:
--   Completed-zeta Taylor coefficients from height-132 quadrature
-- statement:
--   Let $\Lambda_0$ be the regularized completed Riemann zeta function and $L_n$ the published Gaussian-rational coefficient obtained from the height-132 quadrature rule. For every integer $n\ge0$,
--
--   $$
--   \left|\frac{\Lambda_0^{(n)}(1/2+132i)}{n!}-L_n\right|
--   \le\frac{18}{10^{82}2^n}.
--   $$
--
--   This uniformly encloses the exact Taylor coefficients by finite rational expressions. Numerical rounding and zero-location statements require separate certificates.
-- source:
--   Direct oscillatory quadrature and Mellin folding in the theta/Mellin framework due to sometik179 and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHDirect132XiCoefficients
import Mathlib

theorem TaoFivePrimes.rh_direct_132_completed_zeta_coefficients (n : ℕ) :
    ‖iteratedDeriv n completedRiemannZeta₀ ((1/2:ℂ)+132*Complex.I) /
        (n.factorial:ℂ) - RHDirect132XiCoefficients.lambda n‖ ≤
      (18/10^82)/(2:ℝ)^n := by sorry
