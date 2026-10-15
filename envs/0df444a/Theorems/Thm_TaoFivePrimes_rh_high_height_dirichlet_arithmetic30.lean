-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic30
-- name    : TaoFivePrimes.rh_high_height_dirichlet_arithmetic30
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T05:07:29.612129+00:00
-- url     : https://prove2.me/theorems/fb29f67d-0fe6-42e2-b1b0-3647e65bea7f
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_arithmetic30
-- statement:
--   Exact finite arithmetic for Dirichlet terms46081 through47616. It checks the logarithm/phase/exp guards, a quantitative frequency-bin margin, bin<=928, and the proposed128-bit weight/offset/bin integers. No analytic accuracy or RH conclusion is assumed.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletArithmetic
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues30

theorem TaoFivePrimes.rh_high_height_dirichlet_arithmetic30 :
  ∀ c : Nat, c < 96 → ∀ j : Nat, j < 16 →
  let n : Nat := 46081+16*c+j
  let v := RHHighDirichletArithmetic.compute n
  let p : Nat := (((RHHighDirichletValues30.rows[c/32]?).getD [])[16*(c%32)+j]?).getD 0
  RHHighDirichletArithmetic.guard n v=true ∧
  2*(RHHighDirichletArithmetic.delta n).natAbs+2^100≤RHHighLogData.D ∧ RHHighDirichletArithmetic.bin n≤928 ∧
  v.gammaRe=((p%2^160:Nat):Int)-2^159 ∧
  v.gammaIm=((p/2^160%2^160:Nat):Int)-2^159 ∧
  RHHighDirichletArithmetic.delta n=((p/(2^160)^2%2^160:Nat):Int)-2^159 ∧
  RHHighDirichletArithmetic.bin n=p/(2^160)^3 := by sorry
