-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_guards
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_guards
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:11:03.448611+00:00
-- url     : https://prove2.me/theorems/f9d5d5c6-69e9-4f55-9cfc-bc216da19b72
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_guards
-- statement:
--   Combines all33 accepted arithmetic packets into uniform guards for each of the50000 actual finite Dirichlet terms: the analytic enclosure guard, half-bin margin and bin index bound. The proof only partitions the index range and applies the accepted child statements; it does not repeat the finite calculations.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletArithmetic

theorem TaoFivePrimes.rh_batch01_height_dirichlet_guards :
  ∀ n:Nat,1 ≤ n ∧ n≤50000 →
  RHBatch01DirichletArithmetic.guard n (RHBatch01DirichletArithmetic.compute n)=true ∧
  2*(RHBatch01DirichletArithmetic.delta n).natAbs+2^100≤RHBatch01LogData.D ∧
  RHBatch01DirichletArithmetic.bin n≤928 := by sorry
