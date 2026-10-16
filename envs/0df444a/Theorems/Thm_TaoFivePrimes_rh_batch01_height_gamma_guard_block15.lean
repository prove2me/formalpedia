-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block15
-- name    : TaoFivePrimes.rh_batch01_height_gamma_guard_block15
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T17:02:07.106321+00:00
-- url     : https://prove2.me/theorems/b2fdf1da-8d69-4470-8b5f-97ee79365bd3
-- title:
--   TaoFivePrimes.rh_batch01_height_gamma_guard_block15
-- statement:
--   Exact ordinary-kernel verification of the gamma algorithm rounding guards for indices15360 through16383. This is a finite arithmetic result, not an analytic Gamma enclosure or an RH claim.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198, gamma sampling. Exact integer certificates and rounding guards. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01GammaArithmetic

theorem TaoFivePrimes.rh_batch01_height_gamma_guard_block15 :
  ∀ i : Nat, 15360 ≤ i → i < 16384 → RHBatch01GammaGuards.guard (RHBatch01GammaArithmetic.compute i)=true := by sorry
