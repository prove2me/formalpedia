-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_intrinsic_guards
-- name    : TaoFivePrimes.rh_fast_kernel_gamma_intrinsic_guards
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:04:28.161948+00:00
-- url     : https://prove2.me/theorems/bf8e4435-8cf4-45bb-8fef-51e6e420571d
-- title:
--   TaoFivePrimes.rh_fast_kernel_gamma_intrinsic_guards
-- statement:
--   Uniform intrinsic arithmetic conditions of the parameterized gamma program for257≤T≤4294967040 andi<16384. Includes five range clauses, the sine/cosine polynomial subtraction conditions, cosine and exponential-seed positivity, and seed/amplitude upper bounds. No sample enumeration, strict rounded-sine positivity, analytic approximation error, or RH assertion.
-- source:
--   Elementary integer-program bounds in the Platt gamma/Stirling framework, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Original surrounding work: sometik179 c9908072-d99a-4431-aad8-a72c6352619a; Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
open RHFastKernelGammaArithmetic RHFastKernelLogData RHFastKernelGenericExpHorner

theorem TaoFivePrimes.rh_fast_kernel_gamma_intrinsic_guards (T i : Nat) (hT : 257≤T) (hU : T≤4294967040) (hi : i<16384) :
    (compute T i).realPart≤0 ∧
    -100*(D:Int)≤(compute T i).realPart ∧
    (compute T i).period.natAbs≤10000000000 ∧
    2*(compute T i).phaseInput≤D ∧
    2*(compute T i).expInput≤D ∧
    (compute T i).phaseInput^2*horner (cn D) ((compute T i).phaseInput^4)≤
      horner (cp D) ((compute T i).phaseInput^4) ∧
    (compute T i).phaseInput^2*horner (sn D) ((compute T i).phaseInput^4)≤
      horner (sp D) ((compute T i).phaseInput^4) ∧
    0<(compute T i).cos ∧
    0<(compute T i).expSeed ∧
    (compute T i).expSeed≤D ∧ (compute T i).amplitude≤D := by sorry
