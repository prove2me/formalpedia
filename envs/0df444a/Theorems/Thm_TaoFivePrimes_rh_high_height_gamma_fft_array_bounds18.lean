-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fft_array_bounds18
-- name    : TaoFivePrimes.rh_high_height_gamma_fft_array_bounds18
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:49:00.28035+00:00
-- url     : https://prove2.me/theorems/cb9fe0d0-2cc7-4fdf-9e8d-505f77c9a4a2
-- title:
--   TaoFivePrimes.rh_high_height_gamma_fft_array_bounds18
-- statement:
--   Exact shape and magnitude bounds for the two proposed gamma-FFT input matrices at order18:16384 entries,512-entry rows and every biased natural input at most2^167. Checked separately to fit the server verification limit. No analytic, sign, count or RH assertion.
-- source:
--   Existing Platt Fourier construction and Bluestein convolution, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR18
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI18

theorem TaoFivePrimes.rh_high_height_gamma_fft_array_bounds18 :
  ∀ rows∈[RHHighFFTInputR18.rows,RHHighFFTInputI18.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry
