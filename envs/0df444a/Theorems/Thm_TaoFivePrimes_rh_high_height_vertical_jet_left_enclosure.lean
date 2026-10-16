-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_vertical_jet_left_enclosure
-- name    : TaoFivePrimes.rh_high_height_vertical_jet_left_enclosure
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T13:08:43.352965+00:00
-- url     : https://prove2.me/theorems/dfbca228-2200-41fd-9835-7f910c27316f
-- title:
--   TaoFivePrimes.rh_high_height_vertical_jet_left_enclosure
-- statement:
--   All129-by8 actual polynomial jets on this vertical edge are within1e-12 of the corrected512-word table lookup. Combines the accepted55 actual center coefficient bounds,48-term Horner/Taylor soundness and all exact bounded point evaluations. No nonvanishing, winding, zero count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighPolynomialJet
import Definitions.Def_TaoFivePrimes_RHHighContourGridV2

theorem TaoFivePrimes.rh_high_height_vertical_jet_left_enclosure (j k : Nat) (hj:j≤128) (hk:k<8) :
 ‖RHHighPolynomialJet.jet (-64+(-1/2+(j:ℂ)/128)*Complex.I) (Complex.I/128) k-
 RHHighContourVector.value (RHHighContourGridV2.vertical false j k)‖≤1/10^12 := by sorry
