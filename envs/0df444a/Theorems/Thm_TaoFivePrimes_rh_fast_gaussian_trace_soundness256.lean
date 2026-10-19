-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_gaussian_trace_soundness256
-- name    : TaoFivePrimes.rh_fast_gaussian_trace_soundness256
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:52:48.873072+00:00
-- url     : https://prove2.me/theorems/c6a40302-7a8a-42db-a1cf-b28634ab38af
-- title:
--   TaoFivePrimes.rh_fast_gaussian_trace_soundness256
-- statement:
--   A checked40-step exponential Horner trace followed by20 square steps encloses exp(x) at every enclosed real x of magnitude at most65536.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker256
import Definitions.Def_TaoFivePrimes_RHFastComplexBallSemantics
import Mathlib.Analysis.SpecialFunctions.Exponential
open Complex

theorem TaoFivePrimes.rh_fast_gaussian_trace_soundness256 (a:RHFastBallArithmetic.Ball) (x:ℝ)
 (hx:RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D a (x:ℂ))
 (hb:RHFastBallArithmetic.magnitude a+a.radius≤65536*RHFastBallFrequencyChecker256.D)
 (es ss:List RHFastBallArithmetic.Ball)
 (he0:RHFastBallFrequencyChecker256.entry es 0=RHFastBallArithmetic.integer RHFastBallFrequencyChecker256.D 1)
 (hestep:∀n:Nat,n<40→RHFastBallFrequencyChecker256.entry es (n+1)=RHFastBallFrequencyChecker256.expStep
  (RHFastBallArithmetic.divide a (2^20)) n (RHFastBallFrequencyChecker256.entry es n))
 (hs0:RHFastBallFrequencyChecker256.entry ss 0=RHFastBallArithmetic.inflate (RHFastBallFrequencyChecker256.entry es 40) 1)
 (hsstep:∀n:Nat,n<20→RHFastBallFrequencyChecker256.entry ss (n+1)=RHFastBallArithmetic.mul RHFastBallFrequencyChecker256.D
  (RHFastBallFrequencyChecker256.entry ss n) (RHFastBallFrequencyChecker256.entry ss n)) :
 RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D (RHFastBallFrequencyChecker256.entry ss 20)
  ((Real.exp x:ℝ):ℂ) := by sorry
