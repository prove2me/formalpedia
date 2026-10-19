-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_fft_actual_input07
-- name    : TaoFivePrimes.rh_batch01_height_fft_actual_input07
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T12:59:57.295299+00:00
-- url     : https://prove2.me/theorems/0e3211d8-7ea4-4cda-84b3-05f00ff054e7
-- title:
--   TaoFivePrimes.rh_batch01_height_fft_actual_input07
-- statement:
--   All16384 order7 chirped FFT input pairs are exactly the128-bit rational gamma algorithm normalized to80 bits, multiplied by the80-bit indexed chirps. Ordinary sequential16-entry kernel checks are joined to all32 accepted normalized-moment arithmetic packets. This exact arithmetic equality requires separate analytic error and FFT-soundness proofs before a sign or count conclusion.
-- source:
--   Platt DOI10.1090/mcom/3198 and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01NormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputR07
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputI07

theorem TaoFivePrimes.rh_batch01_height_fft_actual_input07 :
  ∀ i : Nat,i<16384 →
  let m:=RHBatch01MomentArithmetic.moment i (RHBatch01GammaArithmetic.compute i) 7
  let c:=RHHighFFTArithmeticBase.chirp i
  (m.1*c.1+m.2*c.2,m.2*c.1-m.1*c.2)=
    ((((((RHBatch01FFTInputR07.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166,
     (((((RHBatch01FFTInputI07.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166) := by sorry
