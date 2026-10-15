-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_real_input_zero_slice31
-- name    : TaoFivePrimes.rh_high_height_real_input_zero_slice31
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:26:10.648111+00:00
-- url     : https://prove2.me/theorems/4032b60e-bdc4-47c0-a85a-a8ecb68d1736
-- title:
--   TaoFivePrimes.rh_high_height_real_input_zero_slice31
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the512 nonzero sparse real-spectrum positions beginning at15872. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRRealZero
import Definitions.Def_TaoFivePrimes_RHHighContourInputIRealZero
import Definitions.Def_TaoFivePrimes_RHHighRealSpectrumZero

theorem TaoFivePrimes.rh_high_height_real_input_zero_slice31 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHHighRealSpectrumZero.rows.flatten RHHighFFTArithmeticBase.chirp (15872+i)=
  ((((((RHHighContourInputRRealZero.rows[31]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHHighContourInputIRealZero.rows[31]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHHighContourInputRRealZero.rows[31]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIRealZero.rows[31]?).getD [])[i]?).getD 0)≤2^167 := by sorry
