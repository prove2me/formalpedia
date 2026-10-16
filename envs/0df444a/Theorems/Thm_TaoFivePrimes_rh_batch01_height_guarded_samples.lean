-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_guarded_samples
-- name    : TaoFivePrimes.rh_batch01_height_guarded_samples
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T18:00:58.43292+00:00
-- url     : https://prove2.me/theorems/457b1aab-42bf-458f-a645-91a3bdefe07d
-- title:
--   TaoFivePrimes.rh_batch01_height_guarded_samples
-- statement:
--   Analytic soundness of the exact rational gamma algorithm and all26 rounded normalized moment orders in the final high-height window, conditional only on its explicit finite arithmetic guard. Gamma error is at most1e-25; each moment error at most1e-23. The separately accepted guard blocks discharge that finite condition. No Fourier evaluation, sign, count or RH conclusion is included.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Ordinary integer log/Taylor and dyadic rounding proof with scaled complex Stirling and factorial-normalized moments. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01GammaArithmetic
import Definitions.Def_TaoFivePrimes_RHBatch01NormalizedMomentArithmetic

theorem TaoFivePrimes.rh_batch01_height_guarded_samples :
  ∀ i : Nat, i < 16384 →
  RHBatch01GammaGuards.guard (RHBatch01GammaArithmetic.compute i)=true →
  let n : Int := (i:Int)-8192
  let b : Nat := (3289999808*32+n).toNat
  let v := RHBatch01GammaArithmetic.compute i
  let D : Nat := RHBatch01LogData.D
  let z : ℂ := ((v.cos:ℂ)+(v.sin:ℂ)*Complex.I)/(D:ℂ)
  let phase : ℂ := if v.negative then starRingEnd ℂ z else z
  ‖(Complex.Gamma (1/4+((b:ℂ)/64)*Complex.I)*
    Complex.exp (((Real.pi*((b:ℝ)/64)/2-((n:ℝ)/32)^2/800:ℝ):ℂ)))-((v.amplitude:ℂ)/(D:ℂ))*phase^8‖≤1/10^25 ∧
  ∀ k : Nat, k < 26 →
    let m := RHBatch01MomentArithmetic.moment i v k
    ‖(Complex.Gamma (1/4+((b:ℂ)/64)*Complex.I)*
    Complex.exp (((Real.pi*((b:ℝ)/64)/2-((n:ℝ)/32)^2/800:ℝ):ℂ)))*((-2*(Real.pi:ℂ)*Complex.I*((n:ℂ)/32))^k/
      ((k.factorial:ℂ)*(512:ℂ)^k))-
      ((m.1:ℂ)+(m.2:ℂ)*Complex.I)/(2:ℂ)^80‖≤1/10^23 := by sorry
