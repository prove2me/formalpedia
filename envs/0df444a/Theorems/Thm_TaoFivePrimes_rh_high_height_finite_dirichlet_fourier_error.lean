-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_finite_dirichlet_fourier_error
-- name    : TaoFivePrimes.rh_high_height_finite_dirichlet_fourier_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T20:28:02.934426+00:00
-- url     : https://prove2.me/theorems/4becc480-415f-4544-8476-8ee85b7bfa88
-- title:
--   TaoFivePrimes.rh_high_height_finite_dirichlet_fourier_error
-- statement:
--   Explicit error for truncating the exact Platt Fourier series after J terms, valid at every real centre T>=0 and positive Gaussian width. The bound uses a chosen contour shift alpha and positive integer moment M, and includes the rational-pole correction. This is an analytic truncation theorem; endpoint arithmetic and the complete RH window count are still separate.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI 10.1090/mcom/3198, Lemma 3.2 and the high-height Fourier architecture. New ordinary Lean derivation of contour rotation, factorial moment envelopes, and the integral-test Dirichlet tail. Original surrounding attribution: sometik179, c9908072-d99a-4431-aad8-a72c6352619a, and Gabewhigham.

import Mathlib
open scoped FourierTransform

theorem TaoFivePrimes.rh_high_height_finite_dirichlet_fourier_error :
  ∀ (T h x α : ℝ) (M J : Nat), 0≤T → 0<h → 0≤α → α<Real.pi/2 → 0<M → 0<J →
  let w : ℝ→ℂ := fun t => Complex.exp ((Real.pi*(t+T)/4-t^2/(2*h^2):ℝ):ℂ)
  let G : ℝ→ℂ := fun t => Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*Complex.I)*w t
  let f : ℝ→ℂ := fun t => completedRiemannZeta (1/2+((t+T:ℝ):ℂ)*Complex.I)*w t
  let d : Nat→ℂ := fun n => Complex.exp (-(1/2+Complex.I*(T:ℂ))*(Real.log ((n+1:ℝ)*Real.sqrt Real.pi):ℂ))*
    𝓕 G (x+Real.log ((n+1:ℝ)*Real.sqrt Real.pi)/(2*Real.pi))
  let C : ℝ := ((4*Real.pi*(M.factorial:ℝ)/(Real.cos α)^M)*Real.exp (
    Real.pi*T/4-T*α/2+h^2/2*(Real.pi/4-α/2)^2+2*(1/4-(M:ℝ))^2/h^2))*
    Real.exp (4*Real.pi*x*(1/4-(M:ℝ)))*Real.pi^(-(M:ℝ))
  ‖𝓕 f x-∑ n ∈ Finset.range J, d n‖ ≤ C*(J:ℝ)^(1-2*(M:ℝ))/(2*(M:ℝ)-1)+
    2*Real.pi*Real.exp (1/(8*h^2)-T^2/(2*h^2)-Real.pi*x) := by sorry
