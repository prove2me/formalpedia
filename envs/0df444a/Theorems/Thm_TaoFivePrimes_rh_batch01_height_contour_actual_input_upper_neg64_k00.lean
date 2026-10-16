-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_actual_input_upper_neg64_k00
-- name    : TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k00
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:13:16.524412+00:00
-- url     : https://prove2.me/theorems/e7364e25-5293-46dd-a9b9-aed94c79b3bf
-- title:
--   TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k00
-- statement:
--   Exact input identities and integer magnitude bounds for all16384 proposed contour FFT inputs, checked in sequential16-entry blocks. A separate analytic spectrum enclosure and DFT soundness theorem are required for any sign, winding or zero-count claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputR00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputI00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K00

theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k00 :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperNeg64K00.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHBatch01ContourInputR00.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHBatch01ContourInputI00.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHBatch01ContourInputR00.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputI00.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by sorry
