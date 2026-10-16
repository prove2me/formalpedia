-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_actual_input_upper_zero_k00_slice00
-- name    : TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k00_slice00
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T10:55:19.14397+00:00
-- url     : https://prove2.me/theorems/1a15104c-d1e7-49b8-b89d-38248f060268
-- title:
--   TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k00_slice00
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the512 nonzero sparse real-spectrum positions beginning at0. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRUpperZeroK00
import Definitions.Def_TaoFivePrimes_RHHighContourInputIUpperZeroK00
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK00

theorem TaoFivePrimes.rh_high_height_contour_actual_input_upper_zero_k00_slice00 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHHighContourSpectrumUpperZeroK00.rows.flatten RHHighFFTArithmeticBase.chirp (0+i)=
  ((((((RHHighContourInputRUpperZeroK00.rows[0]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHHighContourInputIUpperZeroK00.rows[0]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHHighContourInputRUpperZeroK00.rows[0]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIUpperZeroK00.rows[0]?).getD [])[i]?).getD 0)≤2^167 := by sorry
