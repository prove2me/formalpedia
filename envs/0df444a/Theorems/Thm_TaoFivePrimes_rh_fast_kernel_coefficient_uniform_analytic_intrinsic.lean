-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_coefficient_uniform_analytic_intrinsic
-- name    : TaoFivePrimes.rh_fast_kernel_coefficient_uniform_analytic_intrinsic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:21:40.588514+00:00
-- url     : https://prove2.me/theorems/1d12639e-35b7-4493-8b17-24ef7bad5fa1
-- title:
--   TaoFivePrimes.rh_fast_kernel_coefficient_uniform_analytic_intrinsic
-- statement:
--   Uniform completed-zeta Gaussian-window Fourier assembly error≤3e-15 for every natural center3e9≤T≤3.3e9 andm≤1024. Exact grouping of the integer coefficients and numerical gamma Fourier enclosures remain explicit hypotheses. The coefficient mass bound is derived uniformly, with no center-specific mass certificate. No actual table, zero count or RH interval is certified.
-- source:
--   Platt Fourier construction, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Uniform absolute mass is bounded by a telescoping inverse-square-root estimate and the accepted coefficient approximation. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
open scoped FourierTransform

theorem TaoFivePrimes.rh_fast_kernel_coefficient_uniform_analytic_intrinsic (T : Nat) (hT : 3000000000≤T ∧ T≤3300000000)
 (m : Nat) (hm:m≤1024) (B G : Nat→Nat→ℂ)
 (hB:∀b k:Nat,b<929 → k<24 → B b k=
   ∑n:Fin 50000,if RHFastKernelDirichletArithmetic.bin (n.val+1)=b then
    (let c:=RHFastKernelDirichletArithmetic.coefficient T (n.val+1) k
     ((c.1:ℂ)+(c.2:ℂ)*Complex.I)/(2:ℂ)^128) else 0)
 (hF:∀b k:Nat,b<929 → k<24 →
   ‖𝓕 (RHHighSamplingFunctions.moment (T:ℝ) k) (((m+b:Nat):ℝ)/512)‖≤65537)
 (heF:∀b k:Nat,b<929 → k<24 →
   ‖𝓕 (RHHighSamplingFunctions.moment (T:ℝ) k) (((m+b:Nat):ℝ)/512)-G b k‖≤1/10^15) :
 let W : ℝ→ℂ:=fun t=>completedRiemannZeta (1/2+((t+(T:ℝ):ℝ):ℂ)*Complex.I)*
   Complex.exp (((Real.pi*(t+(T:ℝ))/4-t^2/800:ℝ):ℂ))
 ‖(1/512:ℂ)*𝓕 W ((m:ℝ)/512)-
   (1/512:ℂ)*(∑b:Fin 929,∑k:Fin 24,B b.val k.val*G b.val k.val)‖≤3/10^15 := by sorry
