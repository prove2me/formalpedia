-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_fft_array_bounds07
-- name    : TaoFivePrimes.rh_batch01_height_gamma_fft_array_bounds07
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T13:03:53.869226+00:00
-- url     : https://prove2.me/theorems/14d16a17-cc59-40fb-977a-d78eaba8a4ee
-- title:
--   TaoFivePrimes.rh_batch01_height_gamma_fft_array_bounds07
-- statement:
--   Exact shape and magnitude bounds for the two proposed gamma-FFT input matrices at order7:16384 entries,512-entry rows and every biased natural input at most2^167. Checked separately to fit the server verification limit. No analytic, sign, count or RH assertion.
-- source:
--   Existing Platt Fourier construction and Bluestein convolution, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputR07
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputI07

theorem TaoFivePrimes.rh_batch01_height_gamma_fft_array_bounds07 :
  ∀ rows∈[RHBatch01FFTInputR07.rows,RHBatch01FFTInputI07.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry
