-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_real_actual_input_neg64
-- name    : TaoFivePrimes.rh_batch01_height_real_actual_input_neg64
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T18:03:47.117026+00:00
-- url     : https://prove2.me/theorems/3888da63-220d-460b-a7e9-9246305cad02
-- title:
--   TaoFivePrimes.rh_batch01_height_real_actual_input_neg64
-- statement:
--   Exact input identities and integer magnitude bounds for all16384 proposed real-axis FFT inputs, checked in sequential16-entry blocks. A separate analytic spectrum enclosure and DFT soundness theorem are required for any sign, winding or zero-count claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRRealNeg64
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIRealNeg64
import Definitions.Def_TaoFivePrimes_RHBatch01RealSpectrumNeg64

theorem TaoFivePrimes.rh_batch01_height_real_actual_input_neg64 :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHBatch01RealSpectrumNeg64.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHBatch01ContourInputRRealNeg64.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHBatch01ContourInputIRealNeg64.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHBatch01ContourInputRRealNeg64.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIRealNeg64.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by sorry
