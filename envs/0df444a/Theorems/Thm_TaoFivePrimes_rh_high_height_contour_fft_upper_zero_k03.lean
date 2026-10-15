-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_fft_upper_zero_k03
-- name    : TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k03
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:00:49.287993+00:00
-- url     : https://prove2.me/theorems/d56f5b26-3707-465a-858b-2ce1d8bdc69e
-- title:
--   TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k03
-- statement:
--   Exact integer evaluation of the first2048 DFT outputs proposed for the explicit Fourier polynomial on the upper rectangle edge starting atx=0. Three packed convolutions, offset removal and80-bit rounding are checked in Lean. Separate spectrum-accuracy and analytic DFT-soundness proofs are required before any contour or zero-count conclusion.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourInputRUpperZeroK03
import Definitions.Def_TaoFivePrimes_RHHighContourInputIUpperZeroK03
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperZeroK03
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_high_height_contour_fft_upper_zero_k03 :
  RHHighPackedFFT.output RHHighContourInputRUpperZeroK03.rows.flatten RHHighContourInputIUpperZeroK03.rows.flatten
    RHHighFFTChirpR.rows.flatten RHHighFFTChirpI.rows.flatten RHHighFFTChirpS.rows.flatten
    RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighContourOutputUpperZeroK03.rows.flatten := by sorry
