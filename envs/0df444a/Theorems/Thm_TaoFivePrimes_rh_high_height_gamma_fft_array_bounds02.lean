-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fft_array_bounds02
-- name    : TaoFivePrimes.rh_high_height_gamma_fft_array_bounds02
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T07:06:46.547609+00:00
-- url     : https://prove2.me/theorems/2a0945d1-aa70-43a1-a420-a58ba38df375
-- title:
--   TaoFivePrimes.rh_high_height_gamma_fft_array_bounds02
-- statement:
--   Exact shape and magnitude bounds for the two proposed gamma-FFT input matrices at order2:16384 entries,512-entry rows and every biased natural input at most2^167. Checked separately to fit the server verification limit. No analytic, sign, count or RH assertion.
-- source:
--   Existing Platt Fourier construction and Bluestein convolution, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR02
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI02

theorem TaoFivePrimes.rh_high_height_gamma_fft_array_bounds02 :
  ∀ rows∈[RHHighFFTInputR02.rows,RHHighFFTInputI02.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry
