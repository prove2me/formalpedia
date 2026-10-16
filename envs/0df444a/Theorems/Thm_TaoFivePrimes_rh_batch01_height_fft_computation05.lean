-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_fft_computation05
-- name    : TaoFivePrimes.rh_batch01_height_fft_computation05
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T09:48:51.669368+00:00
-- url     : https://prove2.me/theorems/751a5909-eed2-4294-bcae-6d2537d2ddb4
-- title:
--   TaoFivePrimes.rh_batch01_height_fft_computation05
-- statement:
--   Exact integer verification of the first2048 Fourier outputs for the normalized gamma moment order5. Three packed natural-number convolution checks, independently checked input sums, offset removal and80-bit rounding. This arithmetic theorem requires a separate generic DFT soundness and analytic-error proof before it can imply signs or a zero count.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputR05
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputI05
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive05
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_batch01_height_fft_computation05 :
  RHHighPackedFFT.output RHBatch01FFTInputR05.rows.flatten RHBatch01FFTInputI05.rows.flatten
    RHHighFFTChirpR.rows.flatten RHHighFFTChirpI.rows.flatten RHHighFFTChirpS.rows.flatten
    RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHBatch01FFTPositive05.rows.flatten := by sorry
