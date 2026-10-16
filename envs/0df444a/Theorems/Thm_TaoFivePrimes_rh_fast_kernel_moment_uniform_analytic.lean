-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_moment_uniform_analytic
-- name    : TaoFivePrimes.rh_fast_kernel_moment_uniform_analytic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:18:31.105186+00:00
-- url     : https://prove2.me/theorems/a4216ff9-a70f-47e3-885c-4c887f98c21f
-- title:
--   TaoFivePrimes.rh_fast_kernel_moment_uniform_analytic
-- statement:
--   Uniform complex normalized-moment error≤1/10^23 for every natural center3000000256≤T≤3999999744,i<16384,k<26. Uses the public accepted uniform gamma accuracy theorem, the published integer moment program, certified pi and explicit rounding/power perturbation proofs. No finite guard table or per-center analytic proof is assumed. No zero count or RH assertion.
-- source:
--   Platt normalized Fourier moments, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Supporting moment, power and rounding lemmas are carried explicitly from the accepted guarded-sample proof under fresh helper namespaces. Original surrounding work: sometik179 c9908072-d99a-4431-aad8-a72c6352619a; Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHFastKernelNormalizedMomentArithmetic

theorem TaoFivePrimes.rh_fast_kernel_moment_uniform_analytic (T i k : Nat) (hT : 3000000256≤T) (hU : T≤3999999744)
    (hi : i<16384) (hk : k<26) :
  let n : Int := (i:Int)-8192
  let b : Nat := ((T:Int)*32+n).toNat
  let v := RHFastKernelGammaArithmetic.compute T i
  let m := RHFastKernelMomentArithmetic.moment i v k
  ‖(Complex.Gamma (1/4+((b:ℂ)/64)*Complex.I)*
    Complex.exp (((Real.pi*((b:ℝ)/64)/2-((n:ℝ)/32)^2/800:ℝ):ℂ)))*
    ((-2*(Real.pi:ℂ)*Complex.I*((n:ℂ)/32))^k/
      ((k.factorial:ℂ)*(512:ℂ)^k))-
    ((m.1:ℂ)+(m.2:ℂ)*Complex.I)/(2:ℂ)^80‖≤1/10^23 := by sorry
