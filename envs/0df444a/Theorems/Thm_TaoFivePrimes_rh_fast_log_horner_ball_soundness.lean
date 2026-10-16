-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_log_horner_ball_soundness
-- name    : TaoFivePrimes.rh_fast_log_horner_ball_soundness
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:08:14.490522+00:00
-- url     : https://prove2.me/theorems/a4ae62fc-97cc-4adb-9a7d-9b361806fa32
-- title:
--   TaoFivePrimes.rh_fast_log_horner_ball_soundness
-- statement:
--   The public integer-ball Horner program encloses the exact finite odd-denominator polynomial for every positive scale, enclosed complex input, starting index and term count. The analytic logarithm remainder is a separate bound.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastBallSeedPrograms
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
open Complex Finset

theorem TaoFivePrimes.rh_fast_log_horner_ball_soundness (D:Nat) (hD:0<D) (x:RHFastBallArithmetic.Ball) (z:ℂ)
 (hx:RHFastBallSemantics.encloses D x z) (m n:Nat) :
 RHFastBallSemantics.encloses D (RHFastBallSeedPrograms.horner D x m n)
   (∑j∈Finset.range n,z^j/((2*(m+j)+1:Nat):ℂ)) := by sorry
