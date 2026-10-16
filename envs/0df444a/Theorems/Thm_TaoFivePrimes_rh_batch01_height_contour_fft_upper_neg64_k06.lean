-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_fft_upper_neg64_k06
-- name    : TaoFivePrimes.rh_batch01_height_contour_fft_upper_neg64_k06
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:05:11.930321+00:00
-- url     : https://prove2.me/theorems/50c6c985-9d6b-4675-b198-cfbbc69736fd
-- title:
--   TaoFivePrimes.rh_batch01_height_contour_fft_upper_neg64_k06
-- statement:
--   Exact integer evaluation of the first2048 DFT outputs proposed for the explicit Fourier polynomial on the upper rectangle edge starting atx=-64. Three packed convolutions, offset removal and80-bit rounding are checked in Lean. Separate spectrum-accuracy and analytic DFT-soundness proofs are required before any contour or zero-count conclusion.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRUpperNeg64K06
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIUpperNeg64K06
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputUpperNeg64K06
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_batch01_height_contour_fft_upper_neg64_k06 :
  RHHighPackedFFT.output RHBatch01ContourInputRUpperNeg64K06.rows.flatten RHBatch01ContourInputIUpperNeg64K06.rows.flatten
    RHHighFFTChirpR.rows.flatten RHHighFFTChirpI.rows.flatten RHHighFFTChirpS.rows.flatten
    RHHighFFTArithmeticBase.chirp=RHHighPackedFFT.decode RHBatch01ContourOutputUpperNeg64K06.rows.flatten := by sorry
