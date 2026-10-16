-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_intrinsic_guards
-- name    : TaoFivePrimes.rh_fast_kernel_dirichlet_intrinsic_guards
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:39:45.16898+00:00
-- url     : https://prove2.me/theorems/aed6a28d-212e-4052-b623-cca8f6f49add
-- title:
--   TaoFivePrimes.rh_fast_kernel_dirichlet_intrinsic_guards
-- statement:
--   Uniform intrinsic arithmetic conditions for the Dirichlet program at everyT≤4294967040 and1≤n≤50000. Includes real/phase/exp ranges, trigonometric polynomial subtraction bounds, cosine and exponential-seed positivity, seed/amplitude bounds, exponent/dyadic normalization conditions, weak delta bound2|delta|≤D andbin≤1024. No sample enumeration. Does not assert strict rounded-sine positivity, the stronger static margin, bin≤928, analytic accuracy, zero counts or RH.
-- source:
--   Elementary bounds for the existing exact Platt Dirichlet arithmetic, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. All needed nearest-period and scalar range helpers are explicitly included, with only public formal theorem interfaces imported. Original surrounding work: sometik179 c9908072-d99a-4431-aad8-a72c6352619a; Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic
open RHFastKernelGammaArithmetic RHFastKernelLogData RHFastKernelGenericExpHorner

theorem TaoFivePrimes.rh_fast_kernel_dirichlet_intrinsic_guards (T n : Nat) (hT : T≤4294967040) (hn : 0<n) (hN : n≤50000) :
  let v := RHFastKernelDirichletArithmetic.compute T n
  v.realPart≤0 ∧ -100*(D:Int)≤v.realPart ∧
  v.period.natAbs≤10000000000 ∧ 2*v.phaseInput≤D ∧ 2*v.expInput≤D ∧
  v.phaseInput^2*horner (cn D) (v.phaseInput^4)≤horner (cp D) (v.phaseInput^4) ∧
  v.phaseInput^2*horner (sn D) (v.phaseInput^4)≤horner (sp D) (v.phaseInput^4) ∧
  0<v.cos ∧ 0<v.expSeed ∧ v.expSeed≤D ∧ v.amplitude≤D ∧
  RHFastKernelDirichletArithmetic.exponent n≤15 ∧
  2^(RHFastKernelDirichletArithmetic.exponent n)≤n ∧
  n≤2^(RHFastKernelDirichletArithmetic.exponent n+1) ∧
  2*(RHFastKernelDirichletArithmetic.delta n).natAbs≤D ∧
  RHFastKernelDirichletArithmetic.bin n≤1024 := by sorry
