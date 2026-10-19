-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_exponential_trace_soundness256
-- name    : TaoFivePrimes.rh_fast_exponential_trace_soundness256
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:42:27.595112+00:00
-- url     : https://prove2.me/theorems/5fa04be6-54fe-4d23-81a7-4f2a3db97b11
-- title:
--   TaoFivePrimes.rh_fast_exponential_trace_soundness256
-- statement:
--   A40-step integer Horner trace encloses the exact degree40 complex exponential polynomial at its enclosed argument.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker256
import Definitions.Def_TaoFivePrimes_RHFastComplexBallSemantics
import Mathlib.Data.Nat.Factorial.Basic
open Complex Finset

theorem TaoFivePrimes.rh_fast_exponential_trace_soundness256 (zball:RHFastBallArithmetic.Ball) (z:ℂ)
 (hz:RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D zball z)
 (es:List RHFastBallArithmetic.Ball)
 (h0:RHFastBallFrequencyChecker256.entry es 0=RHFastBallArithmetic.integer RHFastBallFrequencyChecker256.D 1)
 (hs:∀n:Nat,n<40→RHFastBallFrequencyChecker256.entry es (n+1)=
  RHFastBallFrequencyChecker256.expStep zball n (RHFastBallFrequencyChecker256.entry es n)) :
 RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D (RHFastBallFrequencyChecker256.entry es 40)
  (∑k∈Finset.range 41,z^k/(k.factorial:ℂ)) := by sorry
