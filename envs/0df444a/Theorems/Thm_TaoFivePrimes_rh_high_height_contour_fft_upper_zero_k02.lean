-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_fft_upper_zero_k02
-- name    : TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k02
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:50:33.194031+00:00
-- url     : https://prove2.me/theorems/1dfb261e-e4c0-4701-8e2a-93cb5c165e7c
-- title:
--   TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k02
-- statement:
--   Exact integer evaluation of the first2048 DFT outputs proposed for the explicit Fourier polynomial on the upper rectangle edge starting atx=0. Three packed convolutions, offset removal and80-bit rounding are checked in Lean. Separate spectrum-accuracy and analytic DFT-soundness proofs are required before any contour or zero-count conclusion.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourInputRUpperZeroK02
import Definitions.Def_TaoFivePrimes_RHHighContourInputIUpperZeroK02
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperZeroK02
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k02 :
  RHHighPackedFFT.output RHHighContourInputRUpperZeroK02.rows.flatten RHHighContourInputIUpperZeroK02.rows.flatten
    RHHighFFTChirpR.rows.flatten RHHighFFTChirpI.rows.flatten RHHighFFTChirpS.rows.flatten
    RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighContourOutputUpperZeroK02.rows.flatten := by sorry
