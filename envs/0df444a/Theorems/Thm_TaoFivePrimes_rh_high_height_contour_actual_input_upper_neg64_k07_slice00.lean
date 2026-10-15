-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_neg64_k07_slice00
-- name    : TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k07_slice00
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:10:21.372997+00:00
-- url     : https://prove2.me/theorems/a991ff97-fc29-439e-9969-bb101f2825ab
-- title:
--   TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k07_slice00
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the512 nonzero sparse real-spectrum positions beginning at0. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRUpperNeg64K07
import Definitions.Def_TaoFivePrimes_RHHighContourInputIUpperNeg64K07
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperNeg64K07

theorem TaoFivePrimes.rh_high_height_contour_actual_input_upper_neg64_k07_slice00 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHHighContourSpectrumUpperNeg64K07.rows.flatten RHHighFFTArithmeticBase.chirp (0+i)=
  ((((((RHHighContourInputRUpperNeg64K07.rows[0]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHHighContourInputIUpperNeg64K07.rows[0]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHHighContourInputRUpperNeg64K07.rows[0]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIUpperNeg64K07.rows[0]?).getD [])[i]?).getD 0)≤2^167 := by sorry
