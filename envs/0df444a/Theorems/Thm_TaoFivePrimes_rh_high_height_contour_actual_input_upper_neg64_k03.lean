-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_neg64_k03
-- name    : TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k03
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T07:06:41.765861+00:00
-- url     : https://prove2.me/theorems/a0f506d3-544b-48d7-a5ec-bbf84542aee7
-- title:
--   TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k03
-- statement:
--   Exact input identities and integer magnitude bounds for all16384 proposed contour FFT inputs, checked in sequential16-entry blocks. A separate analytic spectrum enclosure and DFT soundness theorem are required for any sign, winding or zero-count claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRUpperNeg64K03
import Definitions.Def_TaoFivePrimes_RHHighContourInputIUpperNeg64K03
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperNeg64K03

theorem TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k03 :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHHighContourSpectrumUpperNeg64K03.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHHighContourInputRUpperNeg64K03.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHHighContourInputIUpperNeg64K03.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHHighContourInputRUpperNeg64K03.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIUpperNeg64K03.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by sorry
