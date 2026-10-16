-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_real_part_bounds
-- name    : TaoFivePrimes.rh_fast_kernel_gamma_real_part_bounds
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T18:48:24.567396+00:00
-- url     : https://prove2.me/theorems/8f797c4b-4271-469e-a7d2-4eb663dd1fd4
-- title:
--   TaoFivePrimes.rh_fast_kernel_gamma_real_part_bounds
-- statement:
--   Uniform real-part range bound for the parameterized rational gamma program at all centers257≤T≤4294967040 and all16384 sample indices. The real part lies in[-100D,0]. A symbolic proof using the accepted logarithm upper bound, fraction bounds and integer rounding; no input table. No analytic gamma accuracy or RH assertion.
-- source:
--   Elementary rational bounds on the existing Platt gamma/Stirling arithmetic program (Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198). Original surrounding work: sometik179 c9908072-d99a-4431-aad8-a72c6352619a; Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic

theorem TaoFivePrimes.rh_fast_kernel_gamma_real_part_bounds : ∀ T i : Nat, 257≤T → T≤4294967040 → i<16384 → -100*(RHFastKernelLogData.D:Int)≤(RHFastKernelGammaArithmetic.compute T i).realPart ∧ (RHFastKernelGammaArithmetic.compute T i).realPart≤0 := by sorry
