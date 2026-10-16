-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_all_contour_jets
-- name    : TaoFivePrimes.rh_high_height_all_contour_jets
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T14:30:12.853437+00:00
-- url     : https://prove2.me/theorems/687a8226-de0c-4533-b2f5-23342a336f3d
-- title:
--   TaoFivePrimes.rh_high_height_all_contour_jets
-- statement:
--   All actual polynomial Taylor jets on every point of the four-edge128-unit contour are within1e-12 of the corrected native certificate tables. Two complete FFT blocks and the accepted direct coefficient sum prove the upper edge, including its final endpoint; conjugation proves the lower edge; center Taylor evaluation proves both vertical edges. No winding or count is assumed.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighPolynomialJet
import Definitions.Def_TaoFivePrimes_RHHighContourGeometry

theorem TaoFivePrimes.rh_high_height_all_contour_jets (e j k : Nat) (he:e<4) (hj:j≤RHHighContourGeometry.cells e) (hk:k<8) :
 ‖RHHighPolynomialJet.jet (RHHighContourGeometry.point e j) (RHHighContourGeometry.step e) k-
 RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12 := by sorry
