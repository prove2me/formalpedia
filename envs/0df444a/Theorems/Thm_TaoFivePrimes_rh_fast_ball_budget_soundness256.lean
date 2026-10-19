-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_ball_budget_soundness256
-- name    : TaoFivePrimes.rh_fast_ball_budget_soundness256
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:56:39.573626+00:00
-- url     : https://prove2.me/theorems/16cf97e1-fe67-4ed3-a0b2-108a0471f610
-- title:
--   TaoFivePrimes.rh_fast_ball_budget_soundness256
-- statement:
--   The256-bit integer output budget implies complex error at most5e-16 from the reference integer pair scaled by2^85, whenever the output ball encloses the exact value.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker256
import Definitions.Def_TaoFivePrimes_RHFastComplexBallSemantics
open Complex

theorem TaoFivePrimes.rh_fast_ball_budget_soundness256 (a:RHFastBallArithmetic.Ball) (p:Int×Int) (z:ℂ)
 (ha:RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D a z)
 (hb:RHFastBallFrequencyChecker256.budget a p=true) :
 ‖z-((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^85‖≤1/(2*10^15:ℝ) := by sorry
