-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_samples_16384
-- name    : TaoFivePrimes.rh_high_height_gamma_samples_16384
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T00:15:24.305666+00:00
-- url     : https://prove2.me/theorems/1a60981e-dce1-40f6-ae53-4777b8a9cb10
-- title:
--   TaoFivePrimes.rh_high_height_gamma_samples_16384
-- statement:
--   All 16384 unrounded rational gamma samples in the final 128-unit window at height 3.29 billion have proved norm error at most 1e-25. Includes ordinary integer checks, log and pi error, the scaled Stirling bound, phase reduction, complex Taylor expansion, and rounded amplitude squaring. This does not yet prove the complete Fourier evaluation, endpoint signs, a zero count, or RH on this window.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198, high-height gamma-sampling architecture. Ordinary integer Taylor/logarithm and dyadic rounding proofs. Surrounding mathematical attribution: sometik179 (c9908072-d99a-4431-aad8-a72c6352619a), Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighGammaArithmetic

theorem TaoFivePrimes.rh_high_height_gamma_samples_16384 :
  ∀ i : Nat, i<16384 →
  let n : Int := (i:Int)-8192
  let b : Nat := (3289999936*32+n).toNat
  let v := RHHighGammaArithmetic.compute i
  let D : Nat := RHHighLogData.D
  let z : ℂ := ((v.cos:ℂ)+(v.sin:ℂ)*Complex.I)/(D:ℂ)
  let phase : ℂ := if v.negative then starRingEnd ℂ z else z
  ‖Complex.Gamma (1/4+((b:ℂ)/64)*Complex.I)*
    Complex.exp (((Real.pi*((b:ℝ)/64)/2-((n:ℝ)/32)^2/800:ℝ):ℂ))-
    ((v.amplitude:ℂ)/(D:ℂ))*phase^8‖≤1/10^25 := by sorry
