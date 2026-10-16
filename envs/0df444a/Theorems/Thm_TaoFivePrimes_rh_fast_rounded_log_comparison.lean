-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_rounded_log_comparison
-- name    : TaoFivePrimes.rh_fast_rounded_log_comparison
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T21:35:31.51208+00:00
-- url     : https://prove2.me/theorems/e97e4d95-6919-4c9d-95ad-105ac2da810d
-- title:
--   TaoFivePrimes.rh_fast_rounded_log_comparison
-- statement:
--   Uniform exact comparison: the newly published bounded-intermediate integer logarithm polynomial evaluator differs from the existing homogeneous-polynomial evaluator by at most81 integer units for every natural scaleD and inputs0<q,2p≤q. At scale2^128 this is at most81/2^128 before any later phase amplification. The statement does not claim real-logarithm approximation, gamma accuracy or RH; those bridges remain separate.
-- source:
--   Platt Fourier construction, DOI10.1090/mcom/3198. The arithmetic comparison is a new ordinary Lean induction over rounded Horner evaluation. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHFastRoundedLogArithmetic

theorem TaoFivePrimes.rh_fast_rounded_log_comparison (p q D : Nat) (hq:0<q) (hp:2*p≤q) :
 |(RHFastKernelLogData.rounded p q D:ℚ)-(RHFastRoundedLogArithmetic.rounded p q D:ℚ)|≤81 := by sorry
