-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_static_bins01
-- name    : TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins01
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T21:14:44.205327+00:00
-- url     : https://prove2.me/theorems/6154e3b6-eaca-4e9b-9db1-96c88972b932
-- title:
--   TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins01
-- statement:
--   Center-independent exact arithmetic certificate for every10001≤n≤20000: bin≤928 and twice the normalized delta magnitude plus2^100≤D. The ordinary Lean kernel computes the published rational log/bin program on all10000 indices. Does not assert real-log error, phase/gamma accuracy, a zero count or RH.
-- source:
--   The static log/bin formulas of the existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic

theorem TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins01 (n : Nat) (hn : 10001≤n) (hN : n≤20000) :
  2*(RHFastKernelDirichletArithmetic.delta n).natAbs+2^100≤RHFastKernelLogData.D ∧
  RHFastKernelDirichletArithmetic.bin n≤928 := by sorry
