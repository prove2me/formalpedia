-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_actual_input_upper_neg64_k04_slice00
-- name    : TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k04_slice00
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T23:39:25.59698+00:00
-- url     : https://prove2.me/theorems/63b97ac0-ecf5-442a-aa61-b9fa76542735
-- title:
--   TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k04_slice00
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the512 nonzero sparse real-spectrum positions beginning at0. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRUpperNeg64K04
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIUpperNeg64K04
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K04

theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k04_slice00 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperNeg64K04.rows.flatten RHHighFFTArithmeticBase.chirp (0+i)=
  ((((((RHBatch01ContourInputRUpperNeg64K04.rows[0]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHBatch01ContourInputIUpperNeg64K04.rows[0]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperNeg64K04.rows[0]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperNeg64K04.rows[0]?).getD [])[i]?).getD 0)≤2^167 := by sorry
