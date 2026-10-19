-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_ball_dot_product_soundness256
-- name    : TaoFivePrimes.rh_fast_ball_dot_product_soundness256
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:52:51.192088+00:00
-- url     : https://prove2.me/theorems/57a39246-b8be-4041-a1c0-f8de07c1674c
-- title:
--   TaoFivePrimes.rh_fast_ball_dot_product_soundness256
-- statement:
--   The public integer ball dot product encloses the corresponding finite complex dot product whenever each pair of entries is enclosed.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker256
import Definitions.Def_TaoFivePrimes_RHFastComplexBallSemantics
open Complex Finset

theorem TaoFivePrimes.rh_fast_ball_dot_product_soundness256 (as bs:List RHFastBallArithmetic.Ball) (f g:Nat→ℂ) (hlen:as.length≤bs.length)
 (ha:∀i:Nat,i<as.length→RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D (RHFastBallFrequencyChecker256.entry as i) (f i))
 (hb:∀i:Nat,i<as.length→RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D (RHFastBallFrequencyChecker256.entry bs i) (g i)) :
 RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D (RHFastBallFrequencyChecker256.dot as bs)
  (∑i∈Finset.range as.length,f i*g i) := by sorry
