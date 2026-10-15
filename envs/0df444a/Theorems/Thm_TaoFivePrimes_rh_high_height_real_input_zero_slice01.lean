-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_real_input_zero_slice01
-- name    : TaoFivePrimes.rh_high_height_real_input_zero_slice01
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:08:17.77093+00:00
-- url     : https://prove2.me/theorems/50412f02-2648-4840-97d9-173096c4c751
-- title:
--   TaoFivePrimes.rh_high_height_real_input_zero_slice01
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the512 nonzero sparse real-spectrum positions beginning at512. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRRealZero
import Definitions.Def_TaoFivePrimes_RHHighContourInputIRealZero
import Definitions.Def_TaoFivePrimes_RHHighRealSpectrumZero

theorem TaoFivePrimes.rh_high_height_real_input_zero_slice01 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHHighRealSpectrumZero.rows.flatten RHHighFFTArithmeticBase.chirp (512+i)=
  ((((((RHHighContourInputRRealZero.rows[1]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHHighContourInputIRealZero.rows[1]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHHighContourInputRRealZero.rows[1]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIRealZero.rows[1]?).getD [])[i]?).getD 0)≤2^167 := by sorry
