-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_moment_arithmetic_block26
-- name    : TaoFivePrimes.rh_batch01_height_moment_arithmetic_block26
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:46:42.059081+00:00
-- url     : https://prove2.me/theorems/ef4621e6-6952-4438-93ce-3c09036efc4f
-- title:
--   TaoFivePrimes.rh_batch01_height_moment_arithmetic_block26
-- statement:
--   Exact integer accuracy for26 normalized moment orders at512 gamma samples, indices13312 through13823. All values are checked against the full rational gamma algorithm, using32 separate16-sample kernel proofs. This arithmetic equality makes no analytic, zero-count or RH claim.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Ordinary rational arithmetic and factorial-normalized moments. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01NormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHBatch01MomentValues26

theorem TaoFivePrimes.rh_batch01_height_moment_arithmetic_block26 :
  ∀ c : Nat, c < 32 → ∀ j : Nat, j < 16 → ∀ k : Nat, k < 26 →
  RHBatch01MomentArithmetic.moment (13312+c*16+j) (RHBatch01GammaArithmetic.compute (13312+c*16+j)) k =
  (((((((RHBatch01MomentValues26.rows[c]?).getD [])[j]?).getD 0)/79228162514264337593543950336^(2*k)%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168, ((((((RHBatch01MomentValues26.rows[c]?).getD [])[j]?).getD 0)/79228162514264337593543950336^(2*k+1)%79228162514264337593543950336:Nat):Int)-39614081257132168796771975168) := by sorry
