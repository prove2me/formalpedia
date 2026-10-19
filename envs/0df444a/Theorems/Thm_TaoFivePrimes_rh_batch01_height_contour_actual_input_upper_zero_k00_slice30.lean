-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_actual_input_upper_zero_k00_slice30
-- name    : TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k00_slice30
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T16:11:38.867564+00:00
-- url     : https://prove2.me/theorems/c4867b09-a4ed-4ddb-bf7b-a6a9c9ae40e4
-- title:
--   TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k00_slice30
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the512 nonzero sparse real-spectrum positions beginning at15360. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRUpperZeroK00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIUpperZeroK00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK00

theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k00_slice30 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperZeroK00.rows.flatten RHHighFFTArithmeticBase.chirp (15360+i)=
  ((((((RHBatch01ContourInputRUpperZeroK00.rows[30]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHBatch01ContourInputIUpperZeroK00.rows[30]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperZeroK00.rows[30]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperZeroK00.rows[30]?).getD [])[i]?).getD 0)≤2^167 := by sorry
