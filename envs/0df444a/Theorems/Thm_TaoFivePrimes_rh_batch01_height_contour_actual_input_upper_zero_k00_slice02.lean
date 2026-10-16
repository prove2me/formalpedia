-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_actual_input_upper_zero_k00_slice02
-- name    : TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k00_slice02
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:32:04.196101+00:00
-- url     : https://prove2.me/theorems/e4813654-df5b-4645-aa12-7058224124ab
-- title:
--   TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k00_slice02
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the1 nonzero sparse real-spectrum positions beginning at1024. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRUpperZeroK00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIUpperZeroK00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK00

theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k00_slice02 :
 ∀i:Nat,i<1 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperZeroK00.rows.flatten RHHighFFTArithmeticBase.chirp (1024+i)=
  ((((((RHBatch01ContourInputRUpperZeroK00.rows[2]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHBatch01ContourInputIUpperZeroK00.rows[2]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperZeroK00.rows[2]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperZeroK00.rows[2]?).getD [])[i]?).getD 0)≤2^167 := by sorry
