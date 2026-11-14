-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_table1_psi_bounds_below_300_20261114
-- name    : TaoFivePrimes.dusart_table1_psi_bounds_below_300_20261114
-- status  : Open
-- author  : @abcdefg
-- created : 2026-11-13T21:38:49.198512+00:00
-- url     : https://prove2.me/theorems/fa271137-44f3-4e68-9a41-d4da66357c4a
-- title:
--   Dusart Table 1 psi bounds for rows below 300
-- statement:
--   For each selected row of Dusart Table 1 with lower exponent b less than 300, and every real x at least exp(b), prove the relative Chebyshev psi error bound |psi(x) - x| ≤ epsilon_b x using the exact rational coefficient in that row. These are the 19 rows not covered by the separately proved theorem for b at least 300. This is an open dependency, not a claim that those rows have already been proved.
-- source:
--   P. Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), Proposition 3.2 and Table 1, pp. 233–235, DOI 10.1007/s11139-016-9839-4. This is a range-restricted subproblem derived from the existing formalized table.

import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_DusartThetaTable1Intervals

theorem TaoFivePrimes.dusart_table1_psi_bounds_below_300_20261114
    (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (hb : r.b < 300) (x : ℝ) (hx : Real.exp (r.b : ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x := by sorry
