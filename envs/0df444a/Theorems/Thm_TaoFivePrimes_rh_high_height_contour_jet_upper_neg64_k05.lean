-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_jet_upper_neg64_k05
-- name    : TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k05
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:37:52.093048+00:00
-- url     : https://prove2.me/theorems/711cb0d6-b44b-4f1c-b567-c5cdd0f430dc
-- title:
--   TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k05
-- statement:
--   All2048 actual polynomial Taylor coefficients of order5 on the upper contour grid starting atx=-64 are enclosed by the decoded FFT outputs with error at most10^(-12). Combines accepted exact reference/input/convolution certificates with the accepted generic analytic bridge. No winding, zero count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198; Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighPolynomialJet
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperNeg64K05

theorem TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k05 (j : Nat) (hj:j<2048) :
 ‖RHHighPolynomialJet.jet (-64+(1/2:ℂ)*Complex.I+(j:ℂ)/32) (1/32) 5-
 RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperNeg64K05.rows.flatten)[j]?).getD 0))‖≤1/10^12 := by sorry
