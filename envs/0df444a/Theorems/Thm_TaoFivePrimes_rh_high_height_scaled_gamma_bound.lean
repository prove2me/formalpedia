-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
-- name    : TaoFivePrimes.rh_high_height_scaled_gamma_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T11:01:21.989144+00:00
-- url     : https://prove2.me/theorems/456d4662-d01a-4ab2-92a4-af0e05d6360f
-- title:
--   TaoFivePrimes.rh_high_height_scaled_gamma_bound
-- statement:
--   For every real x, |Gamma(1/4+ix)| exp(pi*x/2) is at most 6. Consequently each Gaussian-windowed Gamma Fourier-kernel moment has the stated explicit polynomial-Gaussian envelope, uniformly in its height center. This is one analytic input to high-height FFT error bounds. It proves no zeta evaluation, sampling theorem, total count or RH window.
-- source:
--   A conservative uniform Gamma bound and Gaussian Fourier-kernel envelope for Platt-style high-height evaluation. Proved directly from Mathlib Gamma convexity, the Beta integral comparison, Euler reflection, conjugation and the exact half-line Gamma norm. Constant 6 is used instead of the sharper constant 4 in Platt 2017 Appendix A.4 (DOI 10.1090/mcom/3198); the theorem does not assert the rest of the algorithm's error estimates. Surrounding xi/theta work: sometik179 (c9908072-d99a-4431-aad8-a72c6352619a) and Gabewhigham.

import Mathlib

theorem TaoFivePrimes.rh_high_height_scaled_gamma_bound :
    (∀ x : ℝ, ‖Complex.Gamma (1/4+(x:ℂ)*Complex.I)‖*Real.exp (Real.pi*x/2)≤6) ∧
    (∀ (T t h : ℝ) (k : Nat),
      ‖Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*Complex.I)*
        (Real.exp (Real.pi*(t+T)/4-t^2/(2*h^2)):ℂ)*
        (-2*(Real.pi:ℂ)*Complex.I*(t:ℂ))^k‖ ≤
        6*(2*Real.pi*|t|)^k*Real.exp (-t^2/(2*h^2))) := by sorry
