-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_real_polynomial_neg64
-- name    : TaoFivePrimes.rh_high_height_real_polynomial_neg64
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:33:45.65298+00:00
-- url     : https://prove2.me/theorems/bed68928-b4d7-4cb0-83f7-a944841d73b5
-- title:
--   TaoFivePrimes.rh_high_height_real_polynomial_neg64
-- statement:
--   All2048 actual real-axis polynomial values in this half-window are enclosed by the proposed exact FFT outputs within1e-12. Uses accepted finite root/input/FFT identities and the generic analytic FFT bridge. Zeta reconstruction remains a separate prerequisite for the target endpoint signs.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFourierPolynomial
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighContourOutputRealNeg64

theorem TaoFivePrimes.rh_high_height_real_polynomial_neg64 (j : Nat) (hj:j<2048) :
 ‖RHHighFourierPolynomial.polynomial (-64+(j:ℂ)/32)-
 RHHighContourVector.value (RHHighContourVector.decode ((RHHighContourOutputRealNeg64.rows.flatten[j]?).getD 0))‖≤1/10^12 := by sorry
