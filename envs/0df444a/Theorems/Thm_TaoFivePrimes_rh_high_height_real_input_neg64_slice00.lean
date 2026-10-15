-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_real_input_neg64_slice00
-- name    : TaoFivePrimes.rh_high_height_real_input_neg64_slice00
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:31:39.723351+00:00
-- url     : https://prove2.me/theorems/9318d877-94dd-4933-bd74-63e8c74ed5e4
-- title:
--   TaoFivePrimes.rh_high_height_real_input_neg64_slice00
-- statement:
--   Exact chirped input identities and167-bit magnitude bounds for the512 nonzero sparse real-spectrum positions beginning at0. Ordinary sequential16-entry kernel checks; no analytic, sign, count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRRealNeg64
import Definitions.Def_TaoFivePrimes_RHHighContourInputIRealNeg64
import Definitions.Def_TaoFivePrimes_RHHighRealSpectrumNeg64

theorem TaoFivePrimes.rh_high_height_real_input_neg64_slice00 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHHighRealSpectrumNeg64.rows.flatten RHHighFFTArithmeticBase.chirp (0+i)=
  ((((((RHHighContourInputRRealNeg64.rows[0]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHHighContourInputIRealNeg64.rows[0]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHHighContourInputRRealNeg64.rows[0]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIRealNeg64.rows[0]?).getD [])[i]?).getD 0)≤2^167 := by sorry
