-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic13
-- name    : TaoFivePrimes.rh_high_height_dirichlet_arithmetic13
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T03:37:37.061353+00:00
-- url     : https://prove2.me/theorems/587c6082-8597-4de7-a9c7-562aa1391fe7
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_arithmetic13
-- statement:
--   Exact finite arithmetic for Dirichlet terms19969 through21504. It checks the logarithm/phase/exp guards, a quantitative frequency-bin margin, bin<=928, and the proposed128-bit weight/offset/bin integers. No analytic accuracy or RH conclusion is assumed.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletArithmetic
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues13

theorem TaoFivePrimes.rh_high_height_dirichlet_arithmetic13 :
  ∀ c : Nat, c < 96 → ∀ j : Nat, j < 16 →
  let n : Nat := 19969+16*c+j
  let v := RHHighDirichletArithmetic.compute n
  let p : Nat := (((RHHighDirichletValues13.rows[c/32]?).getD [])[16*(c%32)+j]?).getD 0
  RHHighDirichletArithmetic.guard n v=true ∧
  2*(RHHighDirichletArithmetic.delta n).natAbs+2^100≤RHHighLogData.D ∧ RHHighDirichletArithmetic.bin n≤928 ∧
  v.gammaRe=((p%2^160:Nat):Int)-2^159 ∧
  v.gammaIm=((p/2^160%2^160:Nat):Int)-2^159 ∧
  RHHighDirichletArithmetic.delta n=((p/(2^160)^2%2^160:Nat):Int)-2^159 ∧
  RHHighDirichletArithmetic.bin n=p/(2^160)^3 := by sorry
