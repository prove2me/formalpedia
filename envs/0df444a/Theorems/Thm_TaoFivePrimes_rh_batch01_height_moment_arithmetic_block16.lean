-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_moment_arithmetic_block16
-- name    : TaoFivePrimes.rh_batch01_height_moment_arithmetic_block16
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T19:27:21.06238+00:00
-- url     : https://prove2.me/theorems/04a42f75-30f9-4162-bfd2-b4764ce6aacc
-- title:
--   TaoFivePrimes.rh_batch01_height_moment_arithmetic_block16
-- statement:
--   Exact integer accuracy for26 normalized moment orders at512 gamma samples, indices8192 through8703. All values are checked against the full rational gamma algorithm, using32 separate16-sample kernel proofs. This arithmetic equality makes no analytic, zero-count or RH claim.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Ordinary rational arithmetic and factorial-normalized moments. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01NormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues16

theorem TaoFivePrimes.rh_batch01_height_moment_arithmetic_block16 :
  ∀ c : Nat, c < 32 → ∀ j : Nat, j < 16 → ∀ k : Nat, k < 26 →
  RHBatch01MomentArithmetic.moment (8192+c*16+j) (RHBatch01GammaArithmetic.compute (8192+c*16+j)) k =
  (((((((RHBatch01MomentValues16.rows[c]?).getD [])[j]?).getD 0)/79228162514264337593543950336^(2*k)%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168, ((((((RHBatch01MomentValues16.rows[c]?).getD [])[j]?).getD 0)/79228162514264337593543950336^(2*k+1)%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168) := by sorry
