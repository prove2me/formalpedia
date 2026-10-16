-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_moment_arithmetic_block23
-- name    : TaoFivePrimes.rh_batch01_height_moment_arithmetic_block23
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:17:51.15961+00:00
-- url     : https://prove2.me/theorems/8c6d4bd6-1c57-4931-b692-a2a33f0e0970
-- title:
--   TaoFivePrimes.rh_batch01_height_moment_arithmetic_block23
-- statement:
--   Exact integer accuracy for26 normalized moment orders at512 gamma samples, indices11776 through12287. All values are checked against the full rational gamma algorithm, using32 separate16-sample kernel proofs. This arithmetic equality makes no analytic, zero-count or RH claim.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Ordinary rational arithmetic and factorial-normalized moments. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01NormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues23

theorem TaoFivePrimes.rh_batch01_height_moment_arithmetic_block23 :
  ∀ c : Nat, c < 32 → ∀ j : Nat, j < 16 → ∀ k : Nat, k < 26 →
  RHBatch01MomentArithmetic.moment (11776+c*16+j) (RHBatch01GammaArithmetic.compute (11776+c*16+j)) k =
  (((((((RHBatch01MomentValues23.rows[c]?).getD [])[j]?).getD 0)/79228162514264337593543950336^(2*k)%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168, ((((((RHBatch01MomentValues23.rows[c]?).getD [])[j]?).getD 0)/79228162514264337593543950336^(2*k+1)%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168) := by sorry
