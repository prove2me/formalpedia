-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_table1_psi_bounds_below_300_except_23_20261114
-- name    : TaoFivePrimes.dusart_table1_psi_bounds_below_300_except_23_20261114
-- status  : Open
-- author  : @abcdefg
-- created : 2026-11-13T21:51:22.731801+00:00
-- url     : https://prove2.me/theorems/141fbd86-e9ec-46e0-9e94-ba831e8973fc
-- title:
--   Dusart Table 1 psi bounds below 300 excluding row 23
-- statement:
--   For each selected Dusart Table 1 row with lower exponent $b<300$ other than $b=23$, prove that every $x\ge e^b$ satisfies $$|\psi(x)-x|\le\varepsilon_b x,$$ with the exact rational coefficient $\varepsilon_b$ encoded for that row. This open statement contains the remaining 18 small rows.
-- source:
--   P. Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), Proposition 3.2 and Table 1, pp. 233–235, DOI 10.1007/s11139-016-9839-4. This is a restriction of the existing formal table theorem.

import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_DusartThetaTable1Intervals

theorem TaoFivePrimes.dusart_table1_psi_bounds_below_300_except_23_20261114
    (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (hb : r.b < 300) (hne : r.b ≠ 23) (x : ℝ) (hx : Real.exp (r.b : ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ)*x := by sorry
