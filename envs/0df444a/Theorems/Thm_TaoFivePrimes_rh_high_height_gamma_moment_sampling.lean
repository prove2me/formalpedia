-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_moment_sampling
-- name    : TaoFivePrimes.rh_high_height_gamma_moment_sampling
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T21:48:05.878575+00:00
-- url     : https://prove2.me/theorems/af691c73-12ef-4fd3-bf40-8eb75012ee67
-- title:
--   TaoFivePrimes.rh_high_height_gamma_moment_sampling
-- statement:
--   Exact Poisson/finite-DFT pair for every factorial-normalized Gaussian gamma moment at h=20. Applies for T>=20, every positive period B and every nonzero transform size N, and includes both time and frequency aliases as convergent sums. Continuity, decay, absolute Fourier summability and all reindexing are proved, not assumed. Numerical Fourier coefficient arithmetic and the RH endpoint signs/count remain separate.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI 10.1090/mcom/3198, Gaussian moment/Poisson architecture. Ordinary Lean proof from Mathlib Poisson summation, explicit gamma contour bounds, a Cauchy integral/Fubini coefficient bound, and integer residue-class reindexing. Original surrounding attribution: sometik179, c9908072-d99a-4431-aad8-a72c6352619a, and Gabewhigham.

import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
open scoped FourierTransform

theorem TaoFivePrimes.rh_high_height_gamma_moment_sampling :
  ∀ (N : Nat) [NeZero N] (T B : ℝ) (k : Nat) (n : Int), 20≤T → 0<B →
  let φ : ℝ→ℂ := fun u => (Complex.Gamma (1/4+(((u+T)/2:ℝ):ℂ)*Complex.I)*
    Complex.exp ((Real.pi*(u+T)/4-u^2/(2*(20:ℝ)^2):ℝ):ℂ)*
      (-2*(Real.pi:ℂ)*Complex.I*(u:ℂ))^k)/((k.factorial:ℂ)*(512:ℂ)^k)
  (∑' q : Int, φ ((n:ℝ)*B/(N:ℝ)+(q:ℝ)*B))=
    (B⁻¹:ℂ)*∑ m : Fin N, (∑' q : Int, 𝓕 φ (((q*(N:Int)+(m.val:Int)):ℝ)/B))*
      Complex.exp (((2*Real.pi*((m.val:ℝ)*(n:ℝ)/(N:ℝ)):ℝ):ℂ)*Complex.I) := by sorry
