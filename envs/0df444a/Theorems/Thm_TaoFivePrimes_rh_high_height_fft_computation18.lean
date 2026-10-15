-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_fft_computation18
-- name    : TaoFivePrimes.rh_high_height_fft_computation18
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T04:57:25.647024+00:00
-- url     : https://prove2.me/theorems/417dd8f4-02fd-41e6-a211-8eb2b703e033
-- title:
--   TaoFivePrimes.rh_high_height_fft_computation18
-- statement:
--   Exact integer verification of the first2048 Fourier outputs for the normalized gamma moment order18. Three packed natural-number convolution checks, independently checked input sums, offset removal and80-bit rounding. This arithmetic theorem requires a separate generic DFT soundness and analytic-error proof before it can imply signs or a zero count.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR18
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI18
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive18
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_high_height_fft_computation18 :
  RHHighPackedFFT.output RHHighFFTInputR18.rows.flatten RHHighFFTInputI18.rows.flatten
    RHHighFFTChirpR.rows.flatten RHHighFFTChirpI.rows.flatten RHHighFFTChirpS.rows.flatten
    RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighFFTPositive18.rows.flatten := by sorry
