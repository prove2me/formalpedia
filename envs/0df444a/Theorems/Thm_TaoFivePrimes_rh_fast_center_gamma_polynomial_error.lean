-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_center_gamma_polynomial_error
-- name    : TaoFivePrimes.rh_fast_center_gamma_polynomial_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T23:06:07.147684+00:00
-- url     : https://prove2.me/theorems/22561c03-bd04-4765-8674-fa7dc6b209ef
-- title:
--   TaoFivePrimes.rh_fast_center_gamma_polynomial_error
-- statement:
--   For every real center3e9≤T≤3.3e9 and|t|≤256, the actual scaled Gamma Gaussian window differs from the center expansion by at most1e-20, under explicit center-anchor error≤1e-25 and increment-norm≤1e-4 hypotheses. The exponential polynomial has degree4 in the degree-seven increment. No Fourier error, numerical table, zero count or RH interval is asserted.
-- source:
--   Gaussian integral and probabilists Hermite identities; center expansion of the first-correction Stirling exponent. Application under investigation: Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Original surrounding mathematical attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
open scoped FourierTransform

theorem TaoFivePrimes.rh_fast_center_gamma_polynomial_error (T t ω:ℝ) (hT:3000000000≤T ∧ T≤3300000000) (ht:|t|≤256)
 (A:ℂ)
 (hA:‖Complex.Gamma (1/4+((T/2:ℝ):ℂ)*Complex.I)*
    Complex.exp (((Real.pi*T/4:ℝ):ℂ))-A‖≤1/10^25)
 (hd:
   let v:ℂ:=1/4+((T/2:ℝ):ℂ)*Complex.I
   let u:ℂ:=((t/2:ℝ):ℂ)*Complex.I
   ‖u*(Complex.log v-1)+(v+u-1/2)*Complex.logTaylor 7 (u/v)+
     (1/(12*v))*((∑j∈Finset.range 7,(-u/v)^j)-1)+
     ((Real.pi*t/4:ℝ):ℂ)-Complex.I*(ω:ℂ)*t‖≤1/10000) :
 let v:ℂ:=1/4+((T/2:ℝ):ℂ)*Complex.I
 let u:ℂ:=((t/2:ℝ):ℂ)*Complex.I
 let d:=u*(Complex.log v-1)+(v+u-1/2)*Complex.logTaylor 7 (u/v)+
     (1/(12*v))*((∑j∈Finset.range 7,(-u/v)^j)-1)+
     ((Real.pi*t/4:ℝ):ℂ)-Complex.I*(ω:ℂ)*t
 ‖Complex.Gamma (1/4+(((T+t)/2:ℝ):ℂ)*Complex.I)*
    Complex.exp (((Real.pi*(T+t)/4-t^2/800:ℝ):ℂ))-
  A*Complex.exp (((-t^2/800:ℝ):ℂ)+Complex.I*(ω:ℂ)*t)*
    (∑k∈Finset.range 5,d^k/(k.factorial:ℂ))‖≤1/10^20 := by sorry
