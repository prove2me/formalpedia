-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k05
-- name    : TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k05
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T13:14:00.872985+00:00
-- url     : https://prove2.me/theorems/89c547d5-3a32-45a2-95e9-dbae69dce627
-- title:
--   TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k05
-- statement:
--   The existing exact16384-entry chirped contour-input identities and magnitude bounds. All five nonzero slices are checked by ordinary16-entry Lean kernel proofs in this single source; the zero middle uses the existing generic argument. No analytic, sign, count, or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRUpperZeroK05
import Definitions.Def_TaoFivePrimes_RHHighContourInputIUpperZeroK05
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK05

theorem TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k05 :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHHighContourSpectrumUpperZeroK05.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHHighContourInputRUpperZeroK05.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHHighContourInputIUpperZeroK05.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHHighContourInputRUpperZeroK05.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIUpperZeroK05.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by sorry
