-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fft_array_bounds23
-- name    : TaoFivePrimes.rh_high_height_gamma_fft_array_bounds23
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:16:31.368859+00:00
-- url     : https://prove2.me/theorems/9d384aa5-463f-43a4-bd7e-3da32bf503f9
-- title:
--   TaoFivePrimes.rh_high_height_gamma_fft_array_bounds23
-- statement:
--   Exact shape and magnitude bounds for the two proposed gamma-FFT input matrices at order23:16384 entries,512-entry rows and every biased natural input at most2^167. Checked separately to fit the server verification limit. No analytic, sign, count or RH assertion.
-- source:
--   Existing Platt Fourier construction and Bluestein convolution, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR23
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI23

theorem TaoFivePrimes.rh_high_height_gamma_fft_array_bounds23 :
  ∀ rows∈[RHHighFFTInputR23.rows,RHHighFFTInputI23.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry
