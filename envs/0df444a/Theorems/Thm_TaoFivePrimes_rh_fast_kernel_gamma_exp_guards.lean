-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_exp_guards
-- name    : TaoFivePrimes.rh_fast_kernel_gamma_exp_guards
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:01:16.968462+00:00
-- url     : https://prove2.me/theorems/a59083fc-fb3d-4234-8949-9389dbf51eb5
-- title:
--   TaoFivePrimes.rh_fast_kernel_gamma_exp_guards
-- statement:
--   Uniform positivity and upper boundD for the negative-exponential seed when2x≤D, and upper boundD after any number of the program scaled-squaring iterations. Coefficientwise Horner comparisons and ordinary natural arithmetic only; no sample enumeration, analytic approximation error or RH assertion.
-- source:
--   Elementary bounds for the existing factorial-normalized exponential program in the Platt gamma/Stirling framework (Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198). Original surrounding work: sometik179 c9908072-d99a-4431-aad8-a72c6352619a; Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic

theorem TaoFivePrimes.rh_fast_kernel_gamma_exp_guards : ∀ x : Nat, 2*x≤RHFastKernelLogData.D → 0<(RHFastKernelNegativeExp.seed RHFastKernelLogData.D x) ∧ (RHFastKernelNegativeExp.seed RHFastKernelLogData.D x)≤RHFastKernelLogData.D ∧ ∀ n : Nat, (List.range n).foldl (fun z _ => z*z/RHFastKernelLogData.D) (RHFastKernelNegativeExp.seed RHFastKernelLogData.D x)≤RHFastKernelLogData.D := by sorry
