-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_fft_actual_input00
-- name    : TaoFivePrimes.rh_batch01_height_fft_actual_input00
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:16:52.851226+00:00
-- url     : https://prove2.me/theorems/73a5f56b-69e5-458a-a940-e033f8218b72
-- title:
--   TaoFivePrimes.rh_batch01_height_fft_actual_input00
-- statement:
--   All16384 order0 chirped FFT input pairs are exactly the128-bit rational gamma algorithm normalized to80 bits, multiplied by the80-bit indexed chirps. Ordinary sequential16-entry kernel checks are joined to all32 accepted normalized-moment arithmetic packets. This exact arithmetic equality requires separate analytic error and FFT-soundness proofs before a sign or count conclusion.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01NormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputR00
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputI00

theorem TaoFivePrimes.rh_batch01_height_fft_actual_input00 :
  ∀ i : Nat,i<16384 →
  let m:=RHBatch01MomentArithmetic.moment i (RHBatch01GammaArithmetic.compute i) 0
  let c:=RHHighFFTArithmeticBase.chirp i
  (m.1*c.1+m.2*c.2,m.2*c.1-m.1*c.2)=
    ((((((RHBatch01FFTInputR00.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166,
     (((((RHBatch01FFTInputI00.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166) := by sorry
