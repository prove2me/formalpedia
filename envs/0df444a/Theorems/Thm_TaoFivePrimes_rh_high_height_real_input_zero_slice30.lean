-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_real_input_zero_slice30
-- name    : TaoFivePrimes.rh_high_height_real_input_zero_slice30
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:22:37.111796+00:00
-- url     : https://prove2.me/theorems/28bbe1a9-7c02-41cb-9a37-67cbc08ab269
-- title:
--   TaoFivePrimes.rh_high_height_real_input_zero_slice30
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the512 nonzero sparse real-spectrum positions beginning at15360. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRRealZero
import Definitions.Def_TaoFivePrimes_RHHighContourInputIRealZero
import Definitions.Def_TaoFivePrimes_RHHighRealSpectrumZero

theorem TaoFivePrimes.rh_high_height_real_input_zero_slice30 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHHighRealSpectrumZero.rows.flatten RHHighFFTArithmeticBase.chirp (15360+i)=
  ((((((RHHighContourInputRRealZero.rows[30]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHHighContourInputIRealZero.rows[30]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHHighContourInputRRealZero.rows[30]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIRealZero.rows[30]?).getD [])[i]?).getD 0)≤2^167 := by sorry
