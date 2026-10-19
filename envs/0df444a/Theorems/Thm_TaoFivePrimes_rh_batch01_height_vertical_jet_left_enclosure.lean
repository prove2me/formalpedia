-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_vertical_jet_left_enclosure
-- name    : TaoFivePrimes.rh_batch01_height_vertical_jet_left_enclosure
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T13:38:02.081455+00:00
-- url     : https://prove2.me/theorems/2e78e62b-821e-41d3-a613-bb7b92c0a697
-- title:
--   TaoFivePrimes.rh_batch01_height_vertical_jet_left_enclosure
-- statement:
--   All129-by8 actual polynomial jets on this vertical edge are within1e-12 of the corrected512-word table lookup. Combines the accepted55 actual center coefficient bounds,48-term Horner/Taylor soundness and all exact bounded point evaluations. No nonvanishing, winding, zero count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01PolynomialJet
import Definitions.Def_TaoFivePrimes_RHBatch01ContourGridV2

theorem TaoFivePrimes.rh_batch01_height_vertical_jet_left_enclosure (j k : Nat) (hj:j≤128) (hk:k<8) :
 ‖RHBatch01PolynomialJet.jet (-64+(-1/2+(j:ℂ)/128)*Complex.I) (Complex.I/128) k-
 RHHighContourVector.value (RHBatch01ContourGridV2.vertical false j k)‖≤1/10^12 := by sorry
