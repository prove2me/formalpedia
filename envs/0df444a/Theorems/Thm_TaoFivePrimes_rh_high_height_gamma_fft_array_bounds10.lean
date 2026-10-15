-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fft_array_bounds10
-- name    : TaoFivePrimes.rh_high_height_gamma_fft_array_bounds10
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:17:13.724179+00:00
-- url     : https://prove2.me/theorems/7a889f67-d324-4c52-a597-18729d26eac4
-- title:
--   TaoFivePrimes.rh_high_height_gamma_fft_array_bounds10
-- statement:
--   Exact shape and magnitude bounds for the two proposed gamma-FFT input matrices at order10:16384 entries,512-entry rows and every biased natural input at most2^167. Checked separately to fit the server verification limit. No analytic, sign, count or RH assertion.
-- source:
--   Existing Platt Fourier construction and Bluestein convolution, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR10
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI10

theorem TaoFivePrimes.rh_high_height_gamma_fft_array_bounds10 :
  ∀ rows∈[RHHighFFTInputR10.rows,RHHighFFTInputI10.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry
