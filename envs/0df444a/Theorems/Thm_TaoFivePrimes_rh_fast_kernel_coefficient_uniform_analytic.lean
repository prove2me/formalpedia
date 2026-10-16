-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_coefficient_uniform_analytic
-- name    : TaoFivePrimes.rh_fast_kernel_coefficient_uniform_analytic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T21:58:39.793719+00:00
-- url     : https://prove2.me/theorems/d506c64d-b486-4cb1-b205-9de13874b052
-- title:
--   TaoFivePrimes.rh_fast_kernel_coefficient_uniform_analytic
-- statement:
--   Uniform completed-zeta Gaussian-window Fourier coefficient assembly error≤3e-15 for every natural center3e9≤T≤3.3e9 and frequency0≤m≤1024. Explicit hypotheses require exact bin grouping, grouped mass≤1024, and gamma-moment Fourier enclosures of error≤1e-15 and norm≤65537. No numerical data identities, signs, zero count or RH window are asserted by this theorem alone.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
open scoped FourierTransform

theorem TaoFivePrimes.rh_fast_kernel_coefficient_uniform_analytic (T : Nat) (hT : 3000000000≤T ∧ T≤3300000000)
 (m : Nat) (hm:m≤1024) (B G : Nat→Nat→ℂ)
 (hB:∀b k:Nat,b<929 → k<24 → B b k=
   ∑n:Fin 50000,if RHFastKernelDirichletArithmetic.bin (n.val+1)=b then
    (let c:=RHFastKernelDirichletArithmetic.coefficient T (n.val+1) k
     ((c.1:ℂ)+(c.2:ℂ)*Complex.I)/(2:ℂ)^128) else 0)
 (hMass:(∑b:Fin 929,∑k:Fin 24,‖B b.val k.val‖)≤1024)
 (hF:∀b k:Nat,b<929 → k<24 →
   ‖𝓕 (RHHighSamplingFunctions.moment (T:ℝ) k) (((m+b:Nat):ℝ)/512)‖≤65537)
 (heF:∀b k:Nat,b<929 → k<24 →
   ‖𝓕 (RHHighSamplingFunctions.moment (T:ℝ) k) (((m+b:Nat):ℝ)/512)-G b k‖≤1/10^15) :
 let W : ℝ→ℂ:=fun t=>completedRiemannZeta (1/2+((t+(T:ℝ):ℝ):ℂ)*Complex.I)*
   Complex.exp (((Real.pi*(t+(T:ℝ))/4-t^2/800:ℝ):ℂ))
 ‖(1/512:ℂ)*𝓕 W ((m:ℝ)/512)-
   (1/512:ℂ)*(∑b:Fin 929,∑k:Fin 24,B b.val k.val*G b.val k.val)‖≤3/10^15 := by sorry
