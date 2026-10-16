-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_local_to_fourier_error
-- name    : TaoFivePrimes.rh_fast_local_to_fourier_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T23:19:56.012429+00:00
-- url     : https://prove2.me/theorems/c18581db-3a5b-462f-988f-9c2229bbb7dd
-- title:
--   TaoFivePrimes.rh_fast_local_to_fourier_error
-- statement:
--   For integrable complex-valued functions with local difference≤81e-20 on|t|≤256 and tail difference≤41exp(-|t|/4), the Fourier transforms differ by at most1e-15 at every real frequency. This is a conditional error-transfer theorem; it does not establish these bounds for any numerical Gamma table or prove an RH interval.
-- source:
--   Gaussian integral and probabilists Hermite identities; center expansion of the first-correction Stirling exponent. Application under investigation: Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Original surrounding mathematical attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
open scoped FourierTransform
open MeasureTheory

theorem TaoFivePrimes.rh_fast_local_to_fourier_error (f g:ℝ→ℂ) (hf:Integrable f) (hg:Integrable g)
 (hl:∀t:ℝ,|t|≤256 → ‖f t-g t‖≤81/10^20)
 (ht:∀t:ℝ,256≤|t| → ‖f t-g t‖≤41*Real.exp (-|t|/4)) (x:ℝ) :
 ‖𝓕 f x-𝓕 g x‖≤1/10^15 := by sorry
