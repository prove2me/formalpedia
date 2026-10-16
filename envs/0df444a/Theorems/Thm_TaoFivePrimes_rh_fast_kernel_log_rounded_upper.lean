-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_log_rounded_upper
-- name    : TaoFivePrimes.rh_fast_kernel_log_rounded_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T18:25:25.097675+00:00
-- url     : https://prove2.me/theorems/79122958-e02e-45a0-899c-3027dbe90c45
-- title:
--   TaoFivePrimes.rh_fast_kernel_log_rounded_upper
-- statement:
--   Uniform upper bound for the rational logarithm program for every natural input and scale with3p≤q. The rounded output is at most its scale, proved by a geometric Horner bound and ordinary verification of the40 coefficient inequalities. No analytic approximation-error or RH assertion.
-- source:
--   Geometric Horner bound for the existing rational logarithm algorithm in the Platt gamma/Stirling framework (Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198). Original surrounding work: sometik179 c9908072-d99a-4431-aad8-a72c6352619a; Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic

theorem TaoFivePrimes.rh_fast_kernel_log_rounded_upper : ∀ p q scale : Nat, 3*p≤q → RHFastKernelLogData.rounded p q scale≤scale := by sorry
