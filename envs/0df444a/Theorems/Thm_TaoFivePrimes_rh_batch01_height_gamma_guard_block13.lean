-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block13
-- name    : TaoFivePrimes.rh_batch01_height_gamma_guard_block13
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T16:54:13.216979+00:00
-- url     : https://prove2.me/theorems/44336148-d533-424e-a7b5-7670432e28c9
-- title:
--   TaoFivePrimes.rh_batch01_height_gamma_guard_block13
-- statement:
--   Exact ordinary-kernel verification of the gamma algorithm rounding guards for indices13312 through14335. This is a finite arithmetic result, not an analytic Gamma enclosure or an RH claim.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198, gamma sampling. Exact integer certificates and rounding guards. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01GammaArithmetic

theorem TaoFivePrimes.rh_batch01_height_gamma_guard_block13 :
  ∀ i : Nat, 13312 ≤ i → i < 14336 → RHBatch01GammaGuards.guard (RHBatch01GammaArithmetic.compute i)=true := by sorry
