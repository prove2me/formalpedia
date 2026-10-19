-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_fft_computation07
-- name    : TaoFivePrimes.rh_batch01_height_fft_computation07
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T13:05:44.195654+00:00
-- url     : https://prove2.me/theorems/e16d9599-b99e-4301-a109-bc46a75972df
-- title:
--   TaoFivePrimes.rh_batch01_height_fft_computation07
-- statement:
--   Exact integer verification of the first2048 Fourier outputs for the normalized gamma moment order7. Three packed natural-number convolution checks, independently checked input sums, offset removal and80-bit rounding. This arithmetic theorem requires a separate generic DFT soundness and analytic-error proof before it can imply signs or a zero count.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputR07
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputI07
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive07
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_batch01_height_fft_computation07 :
  RHHighPackedFFT.output RHBatch01FFTInputR07.rows.flatten RHBatch01FFTInputI07.rows.flatten
    RHHighFFTChirpR.rows.flatten RHHighFFTChirpI.rows.flatten RHHighFFTChirpS.rows.flatten
    RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHBatch01FFTPositive07.rows.flatten := by sorry
