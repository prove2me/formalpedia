-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_fft_actual_input06
-- name    : TaoFivePrimes.rh_batch01_height_fft_actual_input06
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:26:20.041137+00:00
-- url     : https://prove2.me/theorems/e0beba89-c4c6-4f10-8365-10b3ad698c76
-- title:
--   TaoFivePrimes.rh_batch01_height_fft_actual_input06
-- statement:
--   All16384 order6 chirped FFT input pairs are exactly the128-bit rational gamma algorithm normalized to80 bits, multiplied by the80-bit indexed chirps. Ordinary sequential16-entry kernel checks are joined to all32 accepted normalized-moment arithmetic packets. This exact arithmetic equality requires separate analytic error and FFT-soundness proofs before a sign or count conclusion.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01NormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputR06
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputI06

theorem TaoFivePrimes.rh_batch01_height_fft_actual_input06 :
  ∀ i : Nat,i<16384 →
  let m:=RHBatch01MomentArithmetic.moment i (RHBatch01GammaArithmetic.compute i) 6
  let c:=RHHighFFTArithmeticBase.chirp i
  (m.1*c.1+m.2*c.2,m.2*c.1-m.1*c.2)=
    ((((((RHBatch01FFTInputR06.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166,
     (((((RHBatch01FFTInputI06.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166) := by sorry
