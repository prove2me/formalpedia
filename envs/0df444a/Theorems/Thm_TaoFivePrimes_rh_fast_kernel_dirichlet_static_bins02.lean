-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_static_bins02
-- name    : TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins02
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:54:31.929392+00:00
-- url     : https://prove2.me/theorems/6b0cb34c-3717-4f39-989b-9dcb2ed344a0
-- title:
--   TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins02
-- statement:
--   Center-independent exact arithmetic certificate for every20001≤n≤30000: bin≤928 and twice the normalized delta magnitude plus2^100≤D. The ordinary Lean kernel computes the published rational log/bin program on all10000 indices. Does not assert real-log error, phase/gamma accuracy, a zero count or RH.
-- source:
--   The static log/bin formulas of the existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic

theorem TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins02 (n : Nat) (hn : 20001≤n) (hN : n≤30000) :
  2*(RHFastKernelDirichletArithmetic.delta n).natAbs+2^100≤RHFastKernelLogData.D ∧
  RHFastKernelDirichletArithmetic.bin n≤928 := by sorry
