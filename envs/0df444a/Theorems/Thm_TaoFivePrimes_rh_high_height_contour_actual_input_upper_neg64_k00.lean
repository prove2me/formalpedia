-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_neg64_k00
-- name    : TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k00
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T06:27:25.538079+00:00
-- url     : https://prove2.me/theorems/ca657204-72ea-4c00-9d14-fe2d01ed4be7
-- title:
--   TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k00
-- statement:
--   Exact input identities and integer magnitude bounds for all16384 proposed contour FFT inputs, checked in sequential16-entry blocks. A separate analytic spectrum enclosure and DFT soundness theorem are required for any sign, winding or zero-count claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputR00
import Definitions.Def_TaoFivePrimes_RHHighContourInputI00
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperNeg64K00

theorem TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k00 :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHHighContourSpectrumUpperNeg64K00.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHHighContourInputR00.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHHighContourInputI00.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHHighContourInputR00.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputI00.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by sorry
