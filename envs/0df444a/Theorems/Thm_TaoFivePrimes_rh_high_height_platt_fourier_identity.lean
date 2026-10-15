-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_platt_fourier_identity
-- name    : TaoFivePrimes.rh_high_height_platt_fourier_identity
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T20:08:20.112371+00:00
-- url     : https://prove2.me/theorems/d8590610-9a5d-4a13-8f35-f6cba69cf982
-- title:
--   TaoFivePrimes.rh_high_height_platt_fourier_identity
-- statement:
--   Exact Fourier transform of Gaussian-windowed scaled completed Riemann zeta as a convergent infinite series of shifted Gaussian-windowed Gamma transforms, including the explicit rational-pole correction. Holds for every real centre T and positive width h. No finite numerical evaluation or RH window is claimed.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI 10.1090/mcom/3198, Lemma 3.2. Ordinary Lean proof via Mathlib theta/Mellin, Gaussian Fourier transform, Fubini, and explicit pole transforms. Original surrounding attribution: sometik179, c9908072-d99a-4431-aad8-a72c6352619a, and Gabewhigham.

import Mathlib
open scoped FourierTransform

theorem TaoFivePrimes.rh_high_height_platt_fourier_identity :
  ∀ (T h x : ℝ), 0<h →
  let w : ℝ→ℂ := fun t => Complex.exp ((Real.pi*(t+T)/4-t^2/(2*h^2):ℝ):ℂ)
  let G : ℝ→ℂ := fun t => Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*Complex.I)*w t
  𝓕 (fun t : ℝ => completedRiemannZeta (1/2+((t+T:ℝ):ℂ)*Complex.I)*w t) x =
    (∑' n : Nat, Complex.exp (-(1/2+Complex.I*(T:ℂ))*(Real.log ((n+1:ℝ)*Real.sqrt Real.pi):ℂ))*
      𝓕 G (x+Real.log ((n+1:ℝ)*Real.sqrt Real.pi)/(2*Real.pi)))-
    2*(Real.pi:ℂ)*Complex.exp (((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
      Complex.I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ)) := by sorry
