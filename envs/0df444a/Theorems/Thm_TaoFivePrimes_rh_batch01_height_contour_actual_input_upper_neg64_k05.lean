-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_actual_input_upper_neg64_k05
-- name    : TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k05
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T16:58:26.46053+00:00
-- url     : https://prove2.me/theorems/5b155d91-c74a-4f3c-9133-abd6441659a4
-- title:
--   TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k05
-- statement:
--   Exact input identities and integer magnitude bounds for all16384 proposed contour FFT inputs, checked in sequential16-entry blocks. A separate analytic spectrum enclosure and DFT soundness theorem are required for any sign, winding or zero-count claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRUpperNeg64K05
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIUpperNeg64K05
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K05

theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k05 :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperNeg64K05.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHBatch01ContourInputRUpperNeg64K05.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHBatch01ContourInputIUpperNeg64K05.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperNeg64K05.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperNeg64K05.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by sorry
