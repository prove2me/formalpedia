-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_base_guards
-- name    : TaoFivePrimes.rh_fast_kernel_gamma_base_guards
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T19:20:42.928661+00:00
-- url     : https://prove2.me/theorems/c1fc7e6e-3da3-4703-aae3-062c14ea7faf
-- title:
--   TaoFivePrimes.rh_fast_kernel_gamma_base_guards
-- statement:
--   Five uniform basic arithmetic guard clauses for the parameterized gamma program: real-part bounds[-100D,0], period bound1e10, phase-input boundD/2 and exponential-input boundD/2. Covers every center257≤T≤4294967040 and everyi<16384. Symbolic rational and Euclidean-division proofs only; no sample table. Does not assert the remaining positivity clauses of the old Boolean guard, analytic gamma accuracy or RH.
-- source:
--   Elementary rational bounds on the existing Platt gamma/Stirling arithmetic program (Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198). Original surrounding work: sometik179 c9908072-d99a-4431-aad8-a72c6352619a; Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic

theorem TaoFivePrimes.rh_fast_kernel_gamma_base_guards : ∀ T i : Nat, 257≤T → T≤4294967040 → i<16384 → (RHFastKernelGammaArithmetic.compute T i).realPart≤0 ∧ -100*(RHFastKernelLogData.D:Int)≤(RHFastKernelGammaArithmetic.compute T i).realPart ∧ (RHFastKernelGammaArithmetic.compute T i).period.natAbs≤10000000000 ∧ 2*(RHFastKernelGammaArithmetic.compute T i).phaseInput≤RHFastKernelLogData.D ∧ 2*(RHFastKernelGammaArithmetic.compute T i).expInput≤RHFastKernelLogData.D := by sorry
