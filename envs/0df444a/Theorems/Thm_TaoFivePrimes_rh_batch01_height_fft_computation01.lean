-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_fft_computation01
-- name    : TaoFivePrimes.rh_batch01_height_fft_computation01
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:05:03.471658+00:00
-- url     : https://prove2.me/theorems/64d3bd44-dd6f-4d3a-a5fe-78126809d931
-- title:
--   TaoFivePrimes.rh_batch01_height_fft_computation01
-- statement:
--   Exact integer verification of the first2048 Fourier outputs for the normalized gamma moment order1. Three packed natural-number convolution checks, independently checked input sums, offset removal and80-bit rounding. This arithmetic theorem requires a separate generic DFT soundness and analytic-error proof before it can imply signs or a zero count.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputR01
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputI01
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive01
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_batch01_height_fft_computation01 :
  RHHighPackedFFT.output RHBatch01FFTInputR01.rows.flatten RHBatch01FFTInputI01.rows.flatten
    RHHighFFTChirpR.rows.flatten RHHighFFTChirpI.rows.flatten RHHighFFTChirpS.rows.flatten
    RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHBatch01FFTPositive01.rows.flatten := by sorry
