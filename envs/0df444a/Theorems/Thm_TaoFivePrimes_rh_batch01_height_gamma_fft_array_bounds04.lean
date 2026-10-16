-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_fft_array_bounds04
-- name    : TaoFivePrimes.rh_batch01_height_gamma_fft_array_bounds04
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T08:51:13.871991+00:00
-- url     : https://prove2.me/theorems/880cd1c4-9ef9-48d9-ba0f-c863bacf7b12
-- title:
--   TaoFivePrimes.rh_batch01_height_gamma_fft_array_bounds04
-- statement:
--   Exact shape and magnitude bounds for the two proposed gamma-FFT input matrices at order4:16384 entries,512-entry rows and every biased natural input at most2^167. Checked separately to fit the server verification limit. No analytic, sign, count or RH assertion.
-- source:
--   Existing Platt Fourier construction and Bluestein convolution, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputR04
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputI04

theorem TaoFivePrimes.rh_batch01_height_gamma_fft_array_bounds04 :
  ∀ rows∈[RHBatch01FFTInputR04.rows,RHBatch01FFTInputI04.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry
