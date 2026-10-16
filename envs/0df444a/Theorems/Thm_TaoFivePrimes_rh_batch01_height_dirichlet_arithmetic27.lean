-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic27
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic27
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:48:53.608705+00:00
-- url     : https://prove2.me/theorems/ddb46c3c-8cab-42be-be3a-dde44b527d3a
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic27
-- statement:
--   Exact finite arithmetic for Dirichlet terms41473 through43008. It checks the logarithm/phase/exp guards, a quantitative frequency-bin margin, bin<=928, and the proposed128-bit weight/offset/bin integers. No analytic accuracy or RH conclusion is assumed.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletArithmetic
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues27

theorem TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic27 :
  ∀ c : Nat, c < 96 → ∀ j : Nat, j < 16 →
  let n : Nat := 41473+16*c+j
  let v := RHBatch01DirichletArithmetic.compute n
  let p : Nat := (((RHBatch01DirichletValues27.rows[c/32]?).getD [])[16*(c%32)+j]?).getD 0
  RHBatch01DirichletArithmetic.guard n v=true ∧
  2*(RHBatch01DirichletArithmetic.delta n).natAbs+2^100≤RHBatch01LogData.D ∧ RHBatch01DirichletArithmetic.bin n≤928 ∧
  v.gammaRe=((p%2^160:Nat):Int)-2^159 ∧
  v.gammaIm=((p/2^160%2^160:Nat):Int)-2^159 ∧
  RHBatch01DirichletArithmetic.delta n=((p/(2^160)^2%2^160:Nat):Int)-2^159 ∧
  RHBatch01DirichletArithmetic.bin n=p/(2^160)^3 := by sorry
