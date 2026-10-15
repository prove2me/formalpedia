-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_fft_actual_input02
-- name    : TaoFivePrimes.rh_high_height_fft_actual_input02
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:10:47.310055+00:00
-- url     : https://prove2.me/theorems/fe2fe4c1-19b9-4c20-90ae-ef65ef8867d0
-- title:
--   TaoFivePrimes.rh_high_height_fft_actual_input02
-- statement:
--   All16384 order2 chirped FFT input pairs are exactly the128-bit rational gamma algorithm normalized to80 bits, multiplied by the80-bit indexed chirps. Ordinary sequential16-entry kernel checks are joined to all32 accepted normalized-moment arithmetic packets. This exact arithmetic equality requires separate analytic error and FFT-soundness proofs before a sign or count conclusion.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighNormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR02
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI02

theorem TaoFivePrimes.rh_high_height_fft_actual_input02 :
  ∀ i : Nat,i<16384 →
  let m:=RHHighMomentArithmetic.moment i (RHHighGammaArithmetic.compute i) 2
  let c:=RHHighFFTArithmeticBase.chirp i
  (m.1*c.1+m.2*c.2,m.2*c.1-m.1*c.2)=
    ((((((RHHighFFTInputR02.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166,
     (((((RHHighFFTInputI02.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166) := by sorry
