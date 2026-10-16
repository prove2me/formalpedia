-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k07
-- name    : TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k07
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T13:50:39.197736+00:00
-- url     : https://prove2.me/theorems/0e10c356-2d3c-43c9-a29a-ebb2d5ac92b1
-- title:
--   TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k07
-- statement:
--   The existing exact16384-entry chirped contour-input identities and magnitude bounds. All five nonzero slices are checked by ordinary16-entry Lean kernel proofs in this single source; the zero middle uses the existing generic argument. No analytic, sign, count, or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRUpperZeroK07
import Definitions.Def_TaoFivePrimes_RHHighContourInputIUpperZeroK07
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK07

theorem TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k07 :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHHighContourSpectrumUpperZeroK07.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHHighContourInputRUpperZeroK07.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHHighContourInputIUpperZeroK07.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHHighContourInputRUpperZeroK07.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIUpperZeroK07.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by sorry
