-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_actual_input_upper_zero_k00
-- name    : TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k00
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T16:55:31.508781+00:00
-- url     : https://prove2.me/theorems/edc568b2-97ac-4f5b-91ee-cb7d1283eb83
-- title:
--   TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k00
-- statement:
--   Exact input identities and integer magnitude bounds for all16384 proposed contour FFT inputs, checked in sequential16-entry blocks. A separate analytic spectrum enclosure and DFT soundness theorem are required for any sign, winding or zero-count claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRUpperZeroK00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIUpperZeroK00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK00

theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k00 :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperZeroK00.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHBatch01ContourInputRUpperZeroK00.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHBatch01ContourInputIUpperZeroK00.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperZeroK00.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperZeroK00.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by sorry
