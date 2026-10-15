-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_real_fft_zero
-- name    : TaoFivePrimes.rh_high_height_real_fft_zero
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:12:55.110545+00:00
-- url     : https://prove2.me/theorems/5877faff-0d05-4a00-bc1a-8375ae1cc1f8
-- title:
--   TaoFivePrimes.rh_high_height_real_fft_zero
-- statement:
--   Exact integer evaluation of the first2048 DFT outputs proposed for the explicit Fourier polynomial on the real axis starting atx=0. Three packed convolutions, offset removal and80-bit rounding are checked in Lean. Separate spectrum-accuracy and analytic DFT-soundness proofs are required before any contour or zero-count conclusion.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourInputRRealZero
import Definitions.Def_TaoFivePrimes_RHHighContourInputIRealZero
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourOutputRealZero
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_high_height_real_fft_zero :
  RHHighPackedFFT.output RHHighContourInputRRealZero.rows.flatten RHHighContourInputIRealZero.rows.flatten
    RHHighFFTChirpR.rows.flatten RHHighFFTChirpI.rows.flatten RHHighFFTChirpS.rows.flatten
    RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighContourOutputRealZero.rows.flatten := by sorry
