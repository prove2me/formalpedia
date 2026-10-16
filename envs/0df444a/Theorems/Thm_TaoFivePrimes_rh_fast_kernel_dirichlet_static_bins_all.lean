-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_static_bins_all
-- name    : TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins_all
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T21:40:17.112983+00:00
-- url     : https://prove2.me/theorems/f5565513-0491-4dee-aa66-35100de5d2cf
-- title:
--   TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins_all
-- statement:
--   Combine the five accepted adjacent coefficient-index certificates into the exact static margin/bin bound for every1≤n≤50000. No new numerical computation or RH assertion.
-- source:
--   Platt Fourier construction, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic

theorem TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins_all (n : Nat) (hn : 1≤n ∧ n≤50000) :
  2*(RHFastKernelDirichletArithmetic.delta n).natAbs+2^100≤RHFastKernelLogData.D ∧
  RHFastKernelDirichletArithmetic.bin n≤928 := by sorry
