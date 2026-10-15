-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_neg64_k07_slice30
-- name    : TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k07_slice30
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:36:45.845825+00:00
-- url     : https://prove2.me/theorems/9acfd0f7-75d8-490b-b16f-685ce149a3e3
-- title:
--   TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k07_slice30
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the512 nonzero sparse real-spectrum positions beginning at15360. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRUpperNeg64K07
import Definitions.Def_TaoFivePrimes_RHHighContourInputIUpperNeg64K07
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperNeg64K07

theorem TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k07_slice30 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHHighContourSpectrumUpperNeg64K07.rows.flatten RHHighFFTArithmeticBase.chirp (15360+i)=
  ((((((RHHighContourInputRUpperNeg64K07.rows[30]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHHighContourInputIUpperNeg64K07.rows[30]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHHighContourInputRUpperNeg64K07.rows[30]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIUpperNeg64K07.rows[30]?).getD [])[i]?).getD 0)≤2^167 := by sorry
