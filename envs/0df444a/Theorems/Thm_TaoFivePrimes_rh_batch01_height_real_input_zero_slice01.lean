-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_real_input_zero_slice01
-- name    : TaoFivePrimes.rh_batch01_height_real_input_zero_slice01
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:25:50.726653+00:00
-- url     : https://prove2.me/theorems/ded3de1e-7482-454d-bc4c-57038cbfe78d
-- title:
--   TaoFivePrimes.rh_batch01_height_real_input_zero_slice01
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the512 nonzero sparse real-spectrum positions beginning at512. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRRealZero
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIRealZero
import Definitions.Def_TaoFivePrimes_RHBatch01RealSpectrumZero

theorem TaoFivePrimes.rh_batch01_height_real_input_zero_slice01 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHBatch01RealSpectrumZero.rows.flatten RHHighFFTArithmeticBase.chirp (512+i)=
  ((((((RHBatch01ContourInputRRealZero.rows[1]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHBatch01ContourInputIRealZero.rows[1]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHBatch01ContourInputRRealZero.rows[1]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIRealZero.rows[1]?).getD [])[i]?).getD 0)≤2^167 := by sorry
