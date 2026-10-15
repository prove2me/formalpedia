-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fft_array_bounds14
-- name    : TaoFivePrimes.rh_high_height_gamma_fft_array_bounds14
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:34:48.823342+00:00
-- url     : https://prove2.me/theorems/d32eb018-83bc-4ed3-b76f-5606b35c9bb3
-- title:
--   TaoFivePrimes.rh_high_height_gamma_fft_array_bounds14
-- statement:
--   Exact shape and magnitude bounds for the two proposed gamma-FFT input matrices at order14:16384 entries,512-entry rows and every biased natural input at most2^167. Checked separately to fit the server verification limit. No analytic, sign, count or RH assertion.
-- source:
--   Existing Platt Fourier construction and Bluestein convolution, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR14
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI14

theorem TaoFivePrimes.rh_high_height_gamma_fft_array_bounds14 :
  ∀ rows∈[RHHighFFTInputR14.rows,RHHighFFTInputI14.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry
