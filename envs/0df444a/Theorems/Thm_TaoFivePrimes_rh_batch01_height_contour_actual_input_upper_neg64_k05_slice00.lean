-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_actual_input_upper_neg64_k05_slice00
-- name    : TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k05_slice00
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T09:08:47.337762+00:00
-- url     : https://prove2.me/theorems/14fd7e3b-19cc-4b55-8cac-3ddd0f8c4d4b
-- title:
--   TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k05_slice00
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the512 nonzero sparse real-spectrum positions beginning at0. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRUpperNeg64K05
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIUpperNeg64K05
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K05

theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k05_slice00 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperNeg64K05.rows.flatten RHHighFFTArithmeticBase.chirp (0+i)=
  ((((((RHBatch01ContourInputRUpperNeg64K05.rows[0]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHBatch01ContourInputIUpperNeg64K05.rows[0]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperNeg64K05.rows[0]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperNeg64K05.rows[0]?).getD [])[i]?).getD 0)≤2^167 := by sorry
