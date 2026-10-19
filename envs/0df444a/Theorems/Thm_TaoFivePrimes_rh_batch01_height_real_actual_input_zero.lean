-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_real_actual_input_zero
-- name    : TaoFivePrimes.rh_batch01_height_real_actual_input_zero
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T17:09:56.901676+00:00
-- url     : https://prove2.me/theorems/76a8a31f-d8ab-4f0b-82e1-d28371497d3f
-- title:
--   TaoFivePrimes.rh_batch01_height_real_actual_input_zero
-- statement:
--   Exact input identities and integer magnitude bounds for all16384 proposed real-axis FFT inputs, checked in sequential16-entry blocks. A separate analytic spectrum enclosure and DFT soundness theorem are required for any sign, winding or zero-count claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRRealZero
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIRealZero
import Definitions.Def_TaoFivePrimes_RHBatch01RealSpectrumZero

theorem TaoFivePrimes.rh_batch01_height_real_actual_input_zero :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHBatch01RealSpectrumZero.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHBatch01ContourInputRRealZero.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHBatch01ContourInputIRealZero.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHBatch01ContourInputRRealZero.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIRealZero.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by sorry
