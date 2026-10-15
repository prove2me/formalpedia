-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_neg64_k07_slice01
-- name    : TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k07_slice01
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:23:13.32798+00:00
-- url     : https://prove2.me/theorems/4076daa2-4a22-4d49-8175-0b2f36a30d2f
-- title:
--   TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k07_slice01
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the512 nonzero sparse real-spectrum positions beginning at512. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRUpperNeg64K07
import Definitions.Def_TaoFivePrimes_RHHighContourInputIUpperNeg64K07
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperNeg64K07

theorem TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k07_slice01 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHHighContourSpectrumUpperNeg64K07.rows.flatten RHHighFFTArithmeticBase.chirp (512+i)=
  ((((((RHHighContourInputRUpperNeg64K07.rows[1]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHHighContourInputIUpperNeg64K07.rows[1]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHHighContourInputRUpperNeg64K07.rows[1]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIUpperNeg64K07.rows[1]?).getD [])[i]?).getD 0)≤2^167 := by sorry
