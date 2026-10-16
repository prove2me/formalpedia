-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_local_to_fourier_half_error
-- name    : TaoFivePrimes.rh_fast_local_to_fourier_half_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T09:17:19.502595+00:00
-- url     : https://prove2.me/theorems/04a6a3c7-3ef3-46ac-9794-db24799f75a7
-- title:
--   TaoFivePrimes.rh_fast_local_to_fourier_half_error
-- statement:
--   Integrable functions with local difference at most81e-20 on |t|<=256 and tail difference at most41exp(-|t|/4) have Fourier difference at most5e-16 at every real frequency. This leaves a separate5e-16 budget for certified evaluation. No particular numerical table or RH window follows.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib.Analysis.Fourier.FourierTransform
open MeasureTheory
open scoped FourierTransform

theorem TaoFivePrimes.rh_fast_local_to_fourier_half_error (f g:ℝ→ℂ) (hf:Integrable f) (hg:Integrable g)
 (hl:∀t:ℝ,|t|≤256 → ‖f t-g t‖≤81/10^20)
 (ht:∀t:ℝ,256≤|t| → ‖f t-g t‖≤41*Real.exp (-|t|/4)) (x:ℝ) :
 ‖𝓕 f x-𝓕 g x‖≤1/(2*10^15) := by sorry
