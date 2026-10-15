-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_real_actual_input_zero
-- name    : TaoFivePrimes.rh_high_height_real_actual_input_zero
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:38:16.414745+00:00
-- url     : https://prove2.me/theorems/f57c44a5-ce96-4de0-9452-aa9e08ce12a9
-- title:
--   TaoFivePrimes.rh_high_height_real_actual_input_zero
-- statement:
--   Exact input identities and integer magnitude bounds for all16384 proposed real-axis FFT inputs, checked in sequential16-entry blocks. A separate analytic spectrum enclosure and DFT soundness theorem are required for any sign, winding or zero-count claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRRealZero
import Definitions.Def_TaoFivePrimes_RHHighContourInputIRealZero
import Definitions.Def_TaoFivePrimes_RHHighRealSpectrumZero

theorem TaoFivePrimes.rh_high_height_real_actual_input_zero :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHHighRealSpectrumZero.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHHighContourInputRRealZero.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHHighContourInputIRealZero.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHHighContourInputRRealZero.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIRealZero.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by sorry
