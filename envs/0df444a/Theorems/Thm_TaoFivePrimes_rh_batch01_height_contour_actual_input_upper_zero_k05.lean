-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_actual_input_upper_zero_k05
-- name    : TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k05
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T09:24:54.991069+00:00
-- url     : https://prove2.me/theorems/b6e7e27b-99a4-408f-865f-996d7e5efe6d
-- title:
--   TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k05
-- statement:
--   The existing exact16384-entry chirped contour-input identities and magnitude bounds. All five nonzero slices are checked by ordinary16-entry Lean kernel proofs in this single source; the zero middle uses the existing generic argument. No analytic, sign, count, or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRUpperZeroK05
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIUpperZeroK05
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK05

theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k05 :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperZeroK05.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHBatch01ContourInputRUpperZeroK05.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHBatch01ContourInputIUpperZeroK05.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperZeroK05.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperZeroK05.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by sorry
