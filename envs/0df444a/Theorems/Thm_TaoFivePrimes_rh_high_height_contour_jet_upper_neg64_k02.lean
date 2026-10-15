-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_jet_upper_neg64_k02
-- name    : TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k02
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:16:27.941292+00:00
-- url     : https://prove2.me/theorems/93ea5520-225b-4133-bbd4-921a84f789e4
-- title:
--   TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k02
-- statement:
--   All2048 actual polynomial Taylor coefficients of order2 on the upper contour grid starting atx=-64 are enclosed by the decoded FFT outputs with error at most10^(-12). Combines accepted exact reference/input/convolution certificates with the accepted generic analytic bridge. No winding, zero count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198; Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighPolynomialJet
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperNeg64K02

theorem TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k02 (j : Nat) (hj:j<2048) :
 ‖RHHighPolynomialJet.jet (-64+(1/2:ℂ)*Complex.I+(j:ℂ)/32) (1/32) 2-
 RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperNeg64K02.rows.flatten)[j]?).getD 0))‖≤1/10^12 := by sorry
