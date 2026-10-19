-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_real_polynomial_zero
-- name    : TaoFivePrimes.rh_batch01_height_real_polynomial_zero
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T17:21:15.466258+00:00
-- url     : https://prove2.me/theorems/52270de1-1b29-4eb5-a9b0-8faa13dd24db
-- title:
--   TaoFivePrimes.rh_batch01_height_real_polynomial_zero
-- statement:
--   All2048 actual real-axis polynomial values in this half-window are enclosed by the proposed exact FFT outputs within1e-12. Uses accepted finite root/input/FFT identities and the generic analytic FFT bridge. Zeta reconstruction remains a separate prerequisite for the target endpoint signs.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01FourierPolynomial
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputRealZero

theorem TaoFivePrimes.rh_batch01_height_real_polynomial_zero (j : Nat) (hj:j<2048) :
 ‖RHBatch01FourierPolynomial.polynomial (0+(j:ℂ)/32)-
 RHHighContourVector.value (RHHighContourVector.decode ((RHBatch01ContourOutputRealZero.rows.flatten[j]?).getD 0))‖≤1/10^12 := by sorry
