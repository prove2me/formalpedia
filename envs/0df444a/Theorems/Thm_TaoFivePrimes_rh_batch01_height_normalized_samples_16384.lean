-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_normalized_samples_16384
-- name    : TaoFivePrimes.rh_batch01_height_normalized_samples_16384
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T18:27:28.757154+00:00
-- url     : https://prove2.me/theorems/ea8cfd83-a7ac-41b4-bbae-e0e84793f966
-- title:
--   TaoFivePrimes.rh_batch01_height_normalized_samples_16384
-- statement:
--   All26 factorial-normalized moment orders at all16384 gamma sampling points have analytic norm error at most1e-23. The guarded analytic result and every finite guard have server-accepted proofs. This theorem asserts no endpoint signs, zero count or RH window.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Ordinary integer log/Taylor and dyadic rounding proof with scaled complex Stirling and factorial-normalized moments. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01GammaArithmetic
import Definitions.Def_TaoFivePrimes_RHBatch01NormalizedMomentArithmetic

theorem TaoFivePrimes.rh_batch01_height_normalized_samples_16384 :
  ∀ i : Nat, i < 16384 →
  let n : Int := (i:Int)-8192
  let b : Nat := (3289999808*32+n).toNat
  let v := RHBatch01GammaArithmetic.compute i
  let D : Nat := RHBatch01LogData.D
  let z : ℂ := ((v.cos:ℂ)+(v.sin:ℂ)*Complex.I)/(D:ℂ)
  let phase : ℂ := if v.negative then starRingEnd ℂ z else z
  ∀ k : Nat, k < 26 →
    let m := RHBatch01MomentArithmetic.moment i v k
    ‖(Complex.Gamma (1/4+((b:ℂ)/64)*Complex.I)*
    Complex.exp (((Real.pi*((b:ℝ)/64)/2-((n:ℝ)/32)^2/800:ℝ):ℂ)))*((-2*(Real.pi:ℂ)*Complex.I*((n:ℂ)/32))^k/
      ((k.factorial:ℂ)*(512:ℂ)^k))-
      ((m.1:ℂ)+(m.2:ℂ)*Complex.I)/(2:ℂ)^80‖≤1/10^23 := by sorry
