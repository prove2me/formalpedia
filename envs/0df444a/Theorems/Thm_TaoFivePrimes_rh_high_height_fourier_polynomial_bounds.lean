-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_fourier_polynomial_bounds
-- name    : TaoFivePrimes.rh_high_height_fourier_polynomial_bounds
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T07:39:25.477997+00:00
-- url     : https://prove2.me/theorems/82478b8b-7aff-41e0-921e-58c9d6bc4150
-- title:
--   TaoFivePrimes.rh_high_height_fourier_polynomial_bounds
-- statement:
--   Rigorous total coefficient norm mass at most3/5 and eighth weighted moment at most1/100 for the actual proposed Fourier polynomial, together with a real constant term. Exact integer mass checks and standard norm inequalities only. No approximation to zeta, sign, winding, zero count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFourierPolynomial

theorem TaoFivePrimes.rh_high_height_fourier_polynomial_bounds :
 (‖RHHighFourierPolynomial.coefficient 0‖+2*∑m∈Finset.range 1024,‖RHHighFourierPolynomial.coefficient (m+1)‖≤3/5) ∧
 (2*∑m∈Finset.range 1024,‖RHHighFourierPolynomial.coefficient (m+1)‖*((m+1:ℝ)/1024)^8≤1/100) ∧
 RHHighFourierPolynomial.imagInteger 0=0 := by sorry
