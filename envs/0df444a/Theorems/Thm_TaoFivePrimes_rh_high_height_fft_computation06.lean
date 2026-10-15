-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_fft_computation06
-- name    : TaoFivePrimes.rh_high_height_fft_computation06
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T03:11:10.819502+00:00
-- url     : https://prove2.me/theorems/b1216008-4df7-484a-948e-4762374f2ac1
-- title:
--   TaoFivePrimes.rh_high_height_fft_computation06
-- statement:
--   Exact integer verification of the first2048 Fourier outputs for the normalized gamma moment order6. Three packed natural-number convolution checks, independently checked input sums, offset removal and80-bit rounding. This arithmetic theorem requires a separate generic DFT soundness and analytic-error proof before it can imply signs or a zero count.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR06
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI06
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive06
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_high_height_fft_computation06 :
  RHHighPackedFFT.output RHHighFFTInputR06.rows.flatten RHHighFFTInputI06.rows.flatten
    RHHighFFTChirpR.rows.flatten RHHighFFTChirpI.rows.flatten RHHighFFTChirpS.rows.flatten
    RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighFFTPositive06.rows.flatten := by sorry
