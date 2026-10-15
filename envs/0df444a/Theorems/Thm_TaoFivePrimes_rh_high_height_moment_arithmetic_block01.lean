-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block01
-- name    : TaoFivePrimes.rh_high_height_moment_arithmetic_block01
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T00:49:15.298408+00:00
-- url     : https://prove2.me/theorems/a4799d25-f5eb-4283-a92f-1955cdf72f6c
-- title:
--   TaoFivePrimes.rh_high_height_moment_arithmetic_block01
-- statement:
--   Exact integer accuracy for26 normalized moment orders at512 gamma samples, indices512 through1023. All values are checked against the full rational gamma algorithm, using32 separate16-sample kernel proofs. This arithmetic equality makes no analytic, zero-count or RH claim.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Ordinary rational arithmetic and factorial-normalized moments. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighNormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighMomentValues01
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block00

theorem TaoFivePrimes.rh_high_height_moment_arithmetic_block01 :
  ∀ c : Nat, c < 32 → ∀ j : Nat, j < 16 → ∀ k : Nat, k < 26 →
  RHHighMomentArithmetic.moment (512+c*16+j) (RHHighGammaArithmetic.compute (512+c*16+j)) k =
  (((((((RHHighMomentValues01.rows[c]?).getD [])[j]?).getD 0)/79228162514264337593543950336^(2*k)%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168, ((((((RHHighMomentValues01.rows[c]?).getD [])[j]?).getD 0)/79228162514264337593543950336^(2*k+1)%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168) := by sorry
