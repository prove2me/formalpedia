-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block14
-- name    : TaoFivePrimes.rh_batch01_height_gamma_guard_block14
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T16:52:57.72527+00:00
-- url     : https://prove2.me/theorems/219c02c6-fc9d-4cdc-93d1-11dad64456ad
-- title:
--   TaoFivePrimes.rh_batch01_height_gamma_guard_block14
-- statement:
--   Exact ordinary-kernel verification of the gamma algorithm rounding guards for indices14336 through15359. This is a finite arithmetic result, not an analytic Gamma enclosure or an RH claim.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198, gamma sampling. Exact integer certificates and rounding guards. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01GammaArithmetic

theorem TaoFivePrimes.rh_batch01_height_gamma_guard_block14 :
  ∀ i : Nat, 14336 ≤ i → i < 15360 → RHBatch01GammaGuards.guard (RHBatch01GammaArithmetic.compute i)=true := by sorry
