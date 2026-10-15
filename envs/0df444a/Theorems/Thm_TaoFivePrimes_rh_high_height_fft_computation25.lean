-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_fft_computation25
-- name    : TaoFivePrimes.rh_high_height_fft_computation25
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T06:25:21.7132+00:00
-- url     : https://prove2.me/theorems/510845d8-2bbf-4c9b-b0e6-24efadd32ac8
-- title:
--   TaoFivePrimes.rh_high_height_fft_computation25
-- statement:
--   Exact integer verification of the first2048 Fourier outputs for the normalized gamma moment order25. Three packed natural-number convolution checks, independently checked input sums, offset removal and80-bit rounding. This arithmetic theorem requires a separate generic DFT soundness and analytic-error proof before it can imply signs or a zero count.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR25
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI25
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive25
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_high_height_fft_computation25 :
  RHHighPackedFFT.output RHHighFFTInputR25.rows.flatten RHHighFFTInputI25.rows.flatten
    RHHighFFTChirpR.rows.flatten RHHighFFTChirpI.rows.flatten RHHighFFTChirpS.rows.flatten
    RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighFFTPositive25.rows.flatten := by sorry
