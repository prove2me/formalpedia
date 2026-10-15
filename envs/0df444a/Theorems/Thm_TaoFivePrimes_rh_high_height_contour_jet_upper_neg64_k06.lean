-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_jet_upper_neg64_k06
-- name    : TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k06
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:44:09.018925+00:00
-- url     : https://prove2.me/theorems/d25d0e6a-f8d6-4e99-bf21-797784b6ae36
-- title:
--   TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k06
-- statement:
--   All2048 actual polynomial Taylor coefficients of order6 on the upper contour grid starting atx=-64 are enclosed by the decoded FFT outputs with error at most10^(-12). Combines accepted exact reference/input/convolution certificates with the accepted generic analytic bridge. No winding, zero count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198; Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighPolynomialJet
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperNeg64K06

theorem TaoFivePrimes.rh_high_height_contour_jet_upper_neg64_k06 (j : Nat) (hj:j<2048) :
 ‖RHHighPolynomialJet.jet (-64+(1/2:ℂ)*Complex.I+(j:ℂ)/32) (1/32) 6-
 RHHighContourVector.value (RHHighContourVector.decode (((RHHighContourOutputUpperNeg64K06.rows.flatten)[j]?).getD 0))‖≤1/10^12 := by sorry
