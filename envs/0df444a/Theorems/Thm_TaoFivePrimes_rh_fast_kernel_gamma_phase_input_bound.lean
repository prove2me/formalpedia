-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_phase_input_bound
-- name    : TaoFivePrimes.rh_fast_kernel_gamma_phase_input_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T18:11:07.689239+00:00
-- url     : https://prove2.me/theorems/cf1fdca0-3899-4c72-baaf-ddc8a29f81dd
-- title:
--   TaoFivePrimes.rh_fast_kernel_gamma_phase_input_bound
-- statement:
--   Uniform arithmetic range bound for the reduced trigonometric phase input of the parameterized gamma program, for every natural center and sample index. A symbolic integer quotient/remainder argument replaces this one finite guard at every point. No analytic gamma accuracy or RH assertion.
-- source:
--   Elementary Euclidean division applied to the gamma phase-reduction program. Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Original surrounding development: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic

theorem TaoFivePrimes.rh_fast_kernel_gamma_phase_input_bound : ∀ T i : Nat, 2*(RHFastKernelGammaArithmetic.compute T i).phaseInput≤RHFastKernelLogData.D := by sorry
