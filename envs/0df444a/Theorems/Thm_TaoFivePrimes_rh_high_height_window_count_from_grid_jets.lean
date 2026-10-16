-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_window_count_from_grid_jets
-- name    : TaoFivePrimes.rh_high_height_window_count_from_grid_jets
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T13:51:38.255987+00:00
-- url     : https://prove2.me/theorems/14382fa4-cd11-4e7d-aeba-d932554c9d66
-- title:
--   TaoFivePrimes.rh_high_height_window_count_from_grid_jets
-- statement:
--   Conditional count bound for the exact128-unit window. All8448 necessary arithmetic-guarded records are assembled in the proof; the kernel independently checks their length, edge/index enumeration, and oriented logarithm sum. Together with the accepted actual Fourier coefficient enclosure and analytic count soundness this yields at most409 distinct zeros PROVIDED the explicit actual1e-12 all-grid-jet hypothesis holds. It does not itself discharge that hypothesis or prove the window or full finite-height RH. Keeping the numerical proof behind this theorem interface avoids the combined-definition publication timeout.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighHeightWindow
import Definitions.Def_TaoFivePrimes_RHHighContourGeometry
import Definitions.Def_TaoFivePrimes_RHHighPolynomialJet

theorem TaoFivePrimes.rh_high_height_window_count_from_grid_jets
 (hjet:∀e j k:Nat,e<4 → j≤RHHighContourGeometry.cells e → k<8 →
  ‖RHHighPolynomialJet.jet (RHHighContourGeometry.point e j) (RHHighContourGeometry.step e) k-
   RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12) :
 (RHHighHeight.windowZeros 3289999872 3290000000).ncard≤409 := by sorry
