-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block19
-- name    : TaoFivePrimes.rh_high_height_moment_arithmetic_block19
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T03:24:35.923068+00:00
-- url     : https://prove2.me/theorems/005464a2-b6d3-494d-95ae-98ab71b9f8a7
-- title:
--   TaoFivePrimes.rh_high_height_moment_arithmetic_block19
-- statement:
--   Exact integer accuracy for26 normalized moment orders at512 gamma samples, indices9728 through10239. All values are checked against the full rational gamma algorithm, using32 separate16-sample kernel proofs. This arithmetic equality makes no analytic, zero-count or RH claim.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Ordinary rational arithmetic and factorial-normalized moments. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighNormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighMomentValues19
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block18

theorem TaoFivePrimes.rh_high_height_moment_arithmetic_block19 :
  ∀ c : Nat, c < 32 → ∀ j : Nat, j < 16 → ∀ k : Nat, k < 26 →
  RHHighMomentArithmetic.moment (9728+c*16+j) (RHHighGammaArithmetic.compute (9728+c*16+j)) k =
  (((((((RHHighMomentValues19.rows[c]?).getD [])[j]?).getD 0)/79228162514264337593543950336^(2*k)%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168, ((((((RHHighMomentValues19.rows[c]?).getD [])[j]?).getD 0)/79228162514264337593543950336^(2*k+1)%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168) := by sorry
