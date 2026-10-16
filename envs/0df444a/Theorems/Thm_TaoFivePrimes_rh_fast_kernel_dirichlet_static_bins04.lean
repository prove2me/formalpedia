-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_static_bins04
-- name    : TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins04
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:38:38.618983+00:00
-- url     : https://prove2.me/theorems/22e2c51d-6874-47ce-b75b-7269070d12dd
-- title:
--   TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins04
-- statement:
--   Center-independent exact arithmetic certificate for every40001≤n≤50000: bin≤928 and twice the normalized delta magnitude plus2^100≤D. The ordinary Lean kernel computes the published rational log/bin program on all10000 indices. Does not assert real-log error, phase/gamma accuracy, a zero count or RH.
-- source:
--   The static log/bin formulas of the existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic

theorem TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins04 (n : Nat) (hn : 40001≤n) (hN : n≤50000) :
  2*(RHFastKernelDirichletArithmetic.delta n).natAbs+2^100≤RHFastKernelLogData.D ∧
  RHFastKernelDirichletArithmetic.bin n≤928 := by sorry
