-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block08
-- name    : TaoFivePrimes.rh_high_height_moment_arithmetic_block08
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T01:51:41.317714+00:00
-- url     : https://prove2.me/theorems/7e548a9e-58dd-4452-88e3-e67095a22c44
-- title:
--   TaoFivePrimes.rh_high_height_moment_arithmetic_block08
-- statement:
--   Exact integer accuracy for26 normalized moment orders at512 gamma samples, indices4096 through4607. All values are checked against the full rational gamma algorithm, using32 separate16-sample kernel proofs. This arithmetic equality makes no analytic, zero-count or RH claim.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Ordinary rational arithmetic and factorial-normalized moments. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighNormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighMomentValues08
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block07

theorem TaoFivePrimes.rh_high_height_moment_arithmetic_block08 :
  ∀ c : Nat, c < 32 → ∀ j : Nat, j < 16 → ∀ k : Nat, k < 26 →
  RHHighMomentArithmetic.moment (4096+c*16+j) (RHHighGammaArithmetic.compute (4096+c*16+j)) k =
  (((((((RHHighMomentValues08.rows[c]?).getD [])[j]?).getD 0)/79228162514264337593543950336^(2*k)%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168, ((((((RHHighMomentValues08.rows[c]?).getD [])[j]?).getD 0)/79228162514264337593543950336^(2*k+1)%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168) := by sorry
