-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_fft_actual_input09
-- name    : TaoFivePrimes.rh_high_height_fft_actual_input09
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:48:15.612653+00:00
-- url     : https://prove2.me/theorems/bf0ef782-32b5-47e7-a395-433c0a3e669f
-- title:
--   TaoFivePrimes.rh_high_height_fft_actual_input09
-- statement:
--   All16384 order9 chirped FFT input pairs are exactly the128-bit rational gamma algorithm normalized to80 bits, multiplied by the80-bit indexed chirps. Ordinary sequential16-entry kernel checks are joined to all32 accepted normalized-moment arithmetic packets. This exact arithmetic equality requires separate analytic error and FFT-soundness proofs before a sign or count conclusion.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighNormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR09
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI09

theorem TaoFivePrimes.rh_high_height_fft_actual_input09 :
  ∀ i : Nat,i<16384 →
  let m:=RHHighMomentArithmetic.moment i (RHHighGammaArithmetic.compute i) 9
  let c:=RHHighFFTArithmeticBase.chirp i
  (m.1*c.1+m.2*c.2,m.2*c.1-m.1*c.2)=
    ((((((RHHighFFTInputR09.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166,
     (((((RHHighFFTInputI09.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166) := by sorry
