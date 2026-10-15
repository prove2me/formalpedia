-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_fft_upper_neg64_k01
-- name    : TaoFivePrimes.rh_high_height_contour_fft_upper_neg64_k01
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T05:18:00.446341+00:00
-- url     : https://prove2.me/theorems/706c56f8-ded9-4c67-bb36-0ebe7585d752
-- title:
--   TaoFivePrimes.rh_high_height_contour_fft_upper_neg64_k01
-- statement:
--   Exact integer evaluation of the first2048 DFT outputs proposed for the explicit Fourier polynomial on the upper rectangle edge starting atx=-64. Three packed convolutions, offset removal and80-bit rounding are checked in Lean. Separate spectrum-accuracy and analytic DFT-soundness proofs are required before any contour or zero-count conclusion.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourInputRUpperNeg64K01
import Definitions.Def_TaoFivePrimes_RHHighContourInputIUpperNeg64K01
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourOutputUpperNeg64K01
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_high_height_contour_fft_upper_neg64_k01 :
  RHHighPackedFFT.output RHHighContourInputRUpperNeg64K01.rows.flatten RHHighContourInputIUpperNeg64K01.rows.flatten
    RHHighFFTChirpR.rows.flatten RHHighFFTChirpI.rows.flatten RHHighFFTChirpS.rows.flatten
    RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHHighContourOutputUpperNeg64K01.rows.flatten := by sorry
