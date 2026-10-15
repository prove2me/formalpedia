-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_fft_computation15
-- name    : TaoFivePrimes.rh_high_height_fft_computation15
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T04:21:40.172255+00:00
-- url     : https://prove2.me/theorems/d942453d-b0f0-4cf5-a8fe-c01f35f6fe04
-- title:
--   TaoFivePrimes.rh_high_height_fft_computation15
-- statement:
--   Exact integer verification of the first2048 Fourier outputs for the normalized gamma moment order15. Three packed natural-number convolution checks, independently checked input sums, offset removal and80-bit rounding. This arithmetic theorem requires a separate generic DFT soundness and analytic-error proof before it can imply signs or a zero count.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR15
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI15
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive15
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_high_height_fft_computation15 :
  RHHighPackedFFT.output RHHighFFTInputR15.rows.flatten RHHighFFTInputI15.rows.flatten
    RHHighFFTChirpR.rows.flatten RHHighFFTChirpI.rows.flatten RHHighFFTChirpS.rows.flatten
    RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighFFTPositive15.rows.flatten := by sorry
