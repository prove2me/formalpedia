-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_center_gamma_polynomial_uniform
-- name    : TaoFivePrimes.rh_fast_center_gamma_polynomial_uniform
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T23:14:26.038775+00:00
-- url     : https://prove2.me/theorems/c5bab450-f1ea-47f7-99c3-1360cfaac9ce
-- title:
--   TaoFivePrimes.rh_fast_center_gamma_polynomial_uniform
-- statement:
--   For every natural center3000000256≤T≤3300000000 and every real|t|≤256, the actual Gamma Gaussian window has a degree28 center-polynomial approximation with absolute error≤1e-20. The anchor is the published integer Gamma program evaluated only at the center. The increment and anchor conditions are discharged by uniform proofs. No finite guard table is assumed. No Fourier error, numerical table, zero count or RH interval is asserted.
-- source:
--   Gaussian integral and probabilists Hermite identities; center expansion of the first-correction Stirling exponent. Application under investigation: Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Original surrounding mathematical attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
open scoped FourierTransform

theorem TaoFivePrimes.rh_fast_center_gamma_polynomial_uniform (T:Nat) (hT:3000000256≤T) (hU:T≤3300000000)
 (t:ℝ) (ht:|t|≤256) :
 let a:=RHFastKernelGammaArithmetic.compute T 8192
 let q:ℂ:=((a.cos:ℂ)+(a.sin:ℂ)*Complex.I)/(RHFastKernelLogData.D:ℂ)
 let phase:ℂ:=if a.negative then starRingEnd ℂ q else q
 let A:ℂ:=((a.amplitude:ℂ)/(RHFastKernelLogData.D:ℂ))*phase^8
 let ω:ℝ:=Real.log ((T:ℝ)/2)/2-1/(48*(T:ℝ)^2)
 let v:ℂ:=1/4+(((T:ℝ)/2:ℝ):ℂ)*Complex.I
 let u:ℂ:=((t/2:ℝ):ℂ)*Complex.I
 let d:ℂ:=u*(Complex.log v-1)+(v+u-1/2)*Complex.logTaylor 7 (u/v)+
     (1/(12*v))*((∑j∈Finset.range 7,(-u/v)^j)-1)+
     ((Real.pi*t/4:ℝ):ℂ)-Complex.I*(ω:ℂ)*t
 ‖Complex.Gamma (1/4+((((T:ℝ)+t)/2:ℝ):ℂ)*Complex.I)*
    Complex.exp (((Real.pi*((T:ℝ)+t)/4-t^2/800:ℝ):ℂ))-
  A*Complex.exp (((-t^2/800:ℝ):ℂ)+Complex.I*(ω:ℂ)*t)*
    (∑k∈Finset.range 5,d^k/(k.factorial:ℂ))‖≤1/10^20 := by sorry
