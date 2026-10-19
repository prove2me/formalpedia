-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_window256_count_from_coefficients_and_jets
-- name    : TaoFivePrimes.rh_fast_window256_count_from_coefficients_and_jets
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T11:22:15.311433+00:00
-- url     : https://prove2.me/theorems/0f97aa71-5149-43af-b45a-63820b5d81c8
-- title:
--   TaoFivePrimes.rh_fast_window256_count_from_coefficients_and_jets
-- statement:
--   Explicit true coefficient accuracy and contour polynomial-jet bounds imply the closed128-unit window has at most409 distinct zeros. No old closed coefficient bound or window count is used.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighHeightWindow
import Definitions.Def_TaoFivePrimes_RHHighContourGeometry
import Definitions.Def_TaoFivePrimes_RHHighPolynomialJet
import Definitions.Def_TaoFivePrimes_RHHighCoefficientFunctions
import Definitions.Def_TaoFivePrimes_RHHighFourierPolynomial
open scoped FourierTransform

theorem TaoFivePrimes.rh_fast_window256_count_from_coefficients_and_jets
 (hcoeff:∀m:Nat,m≤1024 →
  ‖(1/512:ℂ)*𝓕 RHHighFullCoefficient.W ((m:ℝ)/512)-RHHighFourierPolynomial.coefficient m‖≤1/10^14)
 (hjet:∀e j k:Nat,e<4 → j≤RHHighContourGeometry.cells e → k<8 →
  ‖RHHighPolynomialJet.jet (RHHighContourGeometry.point e j) (RHHighContourGeometry.step e) k-
   RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12) :
 (RHHighHeight.windowZeros 3289999872 3290000000).ncard≤409 := by sorry
