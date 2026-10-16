-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k01
-- name    : TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k01
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T12:28:37.067566+00:00
-- url     : https://prove2.me/theorems/b0f531a1-e270-45c9-a175-13a8deb385cc
-- title:
--   TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k01
-- statement:
--   The existing exact16384-entry chirped contour-input identities and magnitude bounds. All five nonzero slices are checked by ordinary16-entry Lean kernel proofs in this single source; the zero middle uses the existing generic argument. No analytic, sign, count, or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRUpperZeroK01
import Definitions.Def_TaoFivePrimes_RHHighContourInputIUpperZeroK01
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK01

theorem TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k01 :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHHighContourSpectrumUpperZeroK01.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHHighContourInputRUpperZeroK01.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHHighContourInputIUpperZeroK01.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHHighContourInputRUpperZeroK01.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIUpperZeroK01.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by sorry
