-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic03
-- name    : TaoFivePrimes.rh_high_height_dirichlet_arithmetic03
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T02:59:08.322271+00:00
-- url     : https://prove2.me/theorems/46271192-3d34-4317-8a1c-12fefe6c5a8c
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_arithmetic03
-- statement:
--   Exact finite arithmetic for Dirichlet terms4609 through6144. It checks the logarithm/phase/exp guards, a quantitative frequency-bin margin, bin<=928, and the proposed128-bit weight/offset/bin integers. No analytic accuracy or RH conclusion is assumed.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletArithmetic
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues03

theorem TaoFivePrimes.rh_high_height_dirichlet_arithmetic03 :
  ∀ c : Nat, c < 96 → ∀ j : Nat, j < 16 →
  let n : Nat := 4609+16*c+j
  let v := RHHighDirichletArithmetic.compute n
  let p : Nat := (((RHHighDirichletValues03.rows[c/32]?).getD [])[16*(c%32)+j]?).getD 0
  RHHighDirichletArithmetic.guard n v=true ∧
  2*(RHHighDirichletArithmetic.delta n).natAbs+2^100≤RHHighLogData.D ∧ RHHighDirichletArithmetic.bin n≤928 ∧
  v.gammaRe=((p%2^160:Nat):Int)-2^159 ∧
  v.gammaIm=((p/2^160%2^160:Nat):Int)-2^159 ∧
  RHHighDirichletArithmetic.delta n=((p/(2^160)^2%2^160:Nat):Int)-2^159 ∧
  RHHighDirichletArithmetic.bin n=p/(2^160)^3 := by sorry
