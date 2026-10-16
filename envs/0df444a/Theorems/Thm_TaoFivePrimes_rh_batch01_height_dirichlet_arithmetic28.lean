-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic28
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic28
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:59:24.796399+00:00
-- url     : https://prove2.me/theorems/6f03c48e-04f4-4afe-949a-0d2afb950276
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic28
-- statement:
--   Exact finite arithmetic for Dirichlet terms43009 through44544. It checks the logarithm/phase/exp guards, a quantitative frequency-bin margin, bin<=928, and the proposed128-bit weight/offset/bin integers. No analytic accuracy or RH conclusion is assumed.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletArithmetic
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues28

theorem TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic28 :
  ∀ c : Nat, c < 96 → ∀ j : Nat, j < 16 →
  let n : Nat := 43009+16*c+j
  let v := RHBatch01DirichletArithmetic.compute n
  let p : Nat := (((RHBatch01DirichletValues28.rows[c/32]?).getD [])[16*(c%32)+j]?).getD 0
  RHBatch01DirichletArithmetic.guard n v=true ∧
  2*(RHBatch01DirichletArithmetic.delta n).natAbs+2^100≤RHBatch01LogData.D ∧ RHBatch01DirichletArithmetic.bin n≤928 ∧
  v.gammaRe=((p%2^160:Nat):Int)-2^159 ∧
  v.gammaIm=((p/2^160%2^160:Nat):Int)-2^159 ∧
  RHBatch01DirichletArithmetic.delta n=((p/(2^160)^2%2^160:Nat):Int)-2^159 ∧
  RHBatch01DirichletArithmetic.bin n=p/(2^160)^3 := by sorry
