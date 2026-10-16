-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_fft_upper_zero_k07
-- name    : TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k07
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T13:52:38.821141+00:00
-- url     : https://prove2.me/theorems/44f56bef-59d6-4fe2-a4ed-1e981605e6f5
-- title:
--   TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k07
-- statement:
--   Exact integer evaluation of the first2048 DFT outputs proposed for the explicit Fourier polynomial on the upper rectangle edge starting atx=0. Three packed convolutions, offset removal and80-bit rounding are checked in Lean. Separate spectrum-accuracy and analytic DFT-soundness proofs are required before any contour or zero-count conclusion.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourInputRUpperZeroK07
import Definitions.Def_TaoFivePrimes_RHHighContourInputIUpperZeroK07
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperZeroK07
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k07 :
  RHHighPackedFFT.output RHHighContourInputRUpperZeroK07.rows.flatten RHHighContourInputIUpperZeroK07.rows.flatten
    RHHighFFTChirpR.rows.flatten RHHighFFTChirpI.rows.flatten RHHighFFTChirpS.rows.flatten
    RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighContourOutputUpperZeroK07.rows.flatten := by sorry
