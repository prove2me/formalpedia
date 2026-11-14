-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_table1_psi_bound_row_23_20261114
-- name    : TaoFivePrimes.dusart_table1_psi_bound_row_23_20261114
-- status  : Open
-- author  : @abcdefg
-- created : 2026-11-13T21:51:20.627714+00:00
-- url     : https://prove2.me/theorems/84ef2b96-4be3-4301-a8d3-b9aeb29e4537
-- title:
--   Dusart Table 1 psi bound for row 23
-- statement:
--   For every real $x\ge e^{23}$, the Chebyshev psi function obeys $$|\psi(x)-x|\le 0.0002431x.$$ This is the $b=23$ row of the selected Dusart Table 1 bounds. The statement is an open dependency; the current local work establishes a reduction to three explicit zero estimates.
-- source:
--   P. Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), Table 1, pp. 234–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib.NumberTheory.Chebyshev

theorem TaoFivePrimes.dusart_table1_psi_bound_row_23_20261114
    (x : ℝ) (hx : Real.exp (23 : ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000 : ℝ)*x := by sorry
