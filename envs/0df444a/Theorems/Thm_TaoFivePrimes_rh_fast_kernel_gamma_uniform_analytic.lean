-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_uniform_analytic
-- name    : TaoFivePrimes.rh_fast_kernel_gamma_uniform_analytic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:09:37.070777+00:00
-- url     : https://prove2.me/theorems/b8cb3a43-7a06-4476-a701-8ffe88b7e09f
-- title:
--   TaoFivePrimes.rh_fast_kernel_gamma_uniform_analytic
-- statement:
--   Uniform complex gamma sample approximation error at most1/10^25 for every natural center3000000256≤T≤3999999744 and every sample indexi<16384. No finite guard certificate assumption. The proof combines symbolic arithmetic guards, logarithm/Stirling error bounds, signed phase quantization and scaled exponential squaring. Does not establish any zero count, RH interval, lower-center logarithm normalization, or full finite-height RH.
-- source:
--   Platt gamma/Stirling and Fourier construction, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Scalar analytic lemmas are carried in full from the accepted guarded-sample proof, with the center-to-sample bridge parameterized and direct uniform polynomial numerator bounds replacing strict rounded-sine positivity. Original surrounding work: sometik179 c9908072-d99a-4431-aad8-a72c6352619a; Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic

theorem TaoFivePrimes.rh_fast_kernel_gamma_uniform_analytic (T i : Nat) (hT : 3000000256≤T) (hU : T≤3999999744) (hi : i<16384) :
  let n : Int := (i:Int)-8192
  let b : Nat := ((T:Int)*32+n).toNat
  let v := RHFastKernelGammaArithmetic.compute T i
  let D : Nat := RHFastKernelLogData.D
  let z : ℂ := ((v.cos:ℂ)+(v.sin:ℂ)*Complex.I)/(D:ℂ)
  let phase : ℂ := if v.negative then starRingEnd ℂ z else z
  ‖(Complex.Gamma (1/4+((b:ℂ)/64)*Complex.I)*
    Complex.exp (((Real.pi*((b:ℝ)/64)/2-((n:ℝ)/32)^2/800:ℝ):ℂ)))-
    ((v.amplitude:ℂ)/(D:ℂ))*phase^8‖≤1/10^25 := by sorry
