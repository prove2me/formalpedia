-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_actual_input_upper_neg64_k04_slice01
-- name    : TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k04_slice01
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T23:40:13.775554+00:00
-- url     : https://prove2.me/theorems/5793c232-dbca-4d84-b335-227c1d6bfbbb
-- title:
--   TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k04_slice01
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the512 nonzero sparse real-spectrum positions beginning at512. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRUpperNeg64K04
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIUpperNeg64K04
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K04

theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k04_slice01 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperNeg64K04.rows.flatten RHHighFFTArithmeticBase.chirp (512+i)=
  ((((((RHBatch01ContourInputRUpperNeg64K04.rows[1]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHBatch01ContourInputIUpperNeg64K04.rows[1]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperNeg64K04.rows[1]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperNeg64K04.rows[1]?).getD [])[i]?).getD 0)≤2^167 := by sorry
