-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_actual_input_upper_zero_k02
-- name    : TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k02
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:46:48.023961+00:00
-- url     : https://prove2.me/theorems/03838d19-3bdf-46f4-9270-539cc904cd8d
-- title:
--   TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k02
-- statement:
--   The existing exact16384-entry chirped contour-input identities and magnitude bounds. All five nonzero slices are checked by ordinary16-entry Lean kernel proofs in this single source; the zero middle uses the existing generic argument. No analytic, sign, count, or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRUpperZeroK02
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIUpperZeroK02
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK02

theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k02 :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperZeroK02.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHBatch01ContourInputRUpperZeroK02.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHBatch01ContourInputIUpperZeroK02.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperZeroK02.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperZeroK02.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by sorry
