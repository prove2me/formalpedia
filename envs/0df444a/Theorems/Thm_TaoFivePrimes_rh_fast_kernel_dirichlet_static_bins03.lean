-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_static_bins03
-- name    : TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins03
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:44:44.38752+00:00
-- url     : https://prove2.me/theorems/d9754714-d162-4346-8b3d-e1bb187bb1e9
-- title:
--   TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins03
-- statement:
--   Center-independent exact arithmetic certificate for every30001≤n≤40000: bin≤928 and twice the normalized delta magnitude plus2^100≤D. The ordinary Lean kernel computes the published rational log/bin program on all10000 indices. Does not assert real-log error, phase/gamma accuracy, a zero count or RH.
-- source:
--   The static log/bin formulas of the existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic

theorem TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins03 (n : Nat) (hn : 30001≤n) (hN : n≤40000) :
  2*(RHFastKernelDirichletArithmetic.delta n).natAbs+2^100≤RHFastKernelLogData.D ∧
  RHFastKernelDirichletArithmetic.bin n≤928 := by sorry
