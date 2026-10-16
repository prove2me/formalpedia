-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_fft_actual_input04
-- name    : TaoFivePrimes.rh_batch01_height_fft_actual_input04
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T23:52:53.224064+00:00
-- url     : https://prove2.me/theorems/09bcf239-ab53-44ce-8b4d-0d7a844fdc1c
-- title:
--   TaoFivePrimes.rh_batch01_height_fft_actual_input04
-- statement:
--   All16384 order4 chirped FFT input pairs are exactly the128-bit rational gamma algorithm normalized to80 bits, multiplied by the80-bit indexed chirps. Ordinary sequential16-entry kernel checks are joined to all32 accepted normalized-moment arithmetic packets. This exact arithmetic equality requires separate analytic error and FFT-soundness proofs before a sign or count conclusion.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01NormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputR04
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputI04

theorem TaoFivePrimes.rh_batch01_height_fft_actual_input04 :
  ∀ i : Nat,i<16384 →
  let m:=RHBatch01MomentArithmetic.moment i (RHBatch01GammaArithmetic.compute i) 4
  let c:=RHHighFFTArithmeticBase.chirp i
  (m.1*c.1+m.2*c.2,m.2*c.1-m.1*c.2)=
    ((((((RHBatch01FFTInputR04.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166,
     (((((RHBatch01FFTInputI04.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166) := by sorry
