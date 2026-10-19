-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_log_ratio_ball_soundness
-- name    : TaoFivePrimes.rh_fast_log_ratio_ball_soundness
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:32:16.120395+00:00
-- url     : https://prove2.me/theorems/2c838e82-d9bc-423e-95b0-48c3933006a4
-- title:
--   TaoFivePrimes.rh_fast_log_ratio_ball_soundness
-- statement:
--   For positive d and d<=n<=2d, the integer logarithm seed program encloses log(n/d).
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastBallSeedPrograms
import Definitions.Def_TaoFivePrimes_RHFastComplexBallSemantics
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem TaoFivePrimes.rh_fast_log_ratio_ball_soundness (n d:Nat) (hd:0<d) (hlo:d ≤ n) (hhi:n ≤ 2*d) :
 RHFastBallSemantics.encloses RHFastBallSeedPrograms.D (RHFastBallSeedPrograms.logRatio n d)
   ((Real.log ((n:ℝ)/(d:ℝ)):ℝ):ℂ) := by sorry
