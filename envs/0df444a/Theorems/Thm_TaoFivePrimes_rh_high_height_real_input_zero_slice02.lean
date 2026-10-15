-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_real_input_zero_slice02
-- name    : TaoFivePrimes.rh_high_height_real_input_zero_slice02
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:16:35.732143+00:00
-- url     : https://prove2.me/theorems/5d49ec80-815a-41f3-8b96-31d1c75f6690
-- title:
--   TaoFivePrimes.rh_high_height_real_input_zero_slice02
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the1 nonzero sparse real-spectrum positions beginning at1024. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRRealZero
import Definitions.Def_TaoFivePrimes_RHHighContourInputIRealZero
import Definitions.Def_TaoFivePrimes_RHHighRealSpectrumZero

theorem TaoFivePrimes.rh_high_height_real_input_zero_slice02 :
 ∀i:Nat,i<1 →
 RHHighContourVector.raw RHHighRealSpectrumZero.rows.flatten RHHighFFTArithmeticBase.chirp (1024+i)=
  ((((((RHHighContourInputRRealZero.rows[2]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHHighContourInputIRealZero.rows[2]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHHighContourInputRRealZero.rows[2]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIRealZero.rows[2]?).getD [])[i]?).getD 0)≤2^167 := by sorry
