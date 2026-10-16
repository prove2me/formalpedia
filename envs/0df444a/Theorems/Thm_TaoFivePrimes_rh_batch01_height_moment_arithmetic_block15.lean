-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_moment_arithmetic_block15
-- name    : TaoFivePrimes.rh_batch01_height_moment_arithmetic_block15
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T19:20:48.45471+00:00
-- url     : https://prove2.me/theorems/219e9f38-4750-4a83-86de-02409333cb52
-- title:
--   TaoFivePrimes.rh_batch01_height_moment_arithmetic_block15
-- statement:
--   Exact integer accuracy for26 normalized moment orders at512 gamma samples, indices7680 through8191. All values are checked against the full rational gamma algorithm, using32 separate16-sample kernel proofs. This arithmetic equality makes no analytic, zero-count or RH claim.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Ordinary rational arithmetic and factorial-normalized moments. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01NormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues15

theorem TaoFivePrimes.rh_batch01_height_moment_arithmetic_block15 :
  ∀ c : Nat, c < 32 → ∀ j : Nat, j < 16 → ∀ k : Nat, k < 26 →
  RHBatch01MomentArithmetic.moment (7680+c*16+j) (RHBatch01GammaArithmetic.compute (7680+c*16+j)) k =
  (((((((RHBatch01MomentValues15.rows[c]?).getD [])[j]?).getD 0)/79228162514264337593543950336^(2*k)%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168, ((((((RHBatch01MomentValues15.rows[c]?).getD [])[j]?).getD 0)/79228162514264337593543950336^(2*k+1)%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168) := by sorry
