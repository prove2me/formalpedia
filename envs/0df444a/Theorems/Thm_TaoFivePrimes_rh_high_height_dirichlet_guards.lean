-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_guards
-- name    : TaoFivePrimes.rh_high_height_dirichlet_guards
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T05:49:43.179349+00:00
-- url     : https://prove2.me/theorems/46737708-2850-4d25-8d33-ec153d8bd878
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_guards
-- statement:
--   Combines all33 accepted arithmetic packets into uniform guards for each of the50000 actual finite Dirichlet terms: the analytic enclosure guard, half-bin margin and bin index bound. The proof only partitions the index range and applies the accepted child statements; it does not repeat the finite calculations.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletArithmetic

theorem TaoFivePrimes.rh_high_height_dirichlet_guards :
  ∀ n:Nat,1 ≤ n ∧ n≤50000 →
  RHHighDirichletArithmetic.guard n (RHHighDirichletArithmetic.compute n)=true ∧
  2*(RHHighDirichletArithmetic.delta n).natAbs+2^100≤RHHighLogData.D ∧
  RHHighDirichletArithmetic.bin n≤928 := by sorry
