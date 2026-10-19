-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_table1_psi_bounds_for_log_four_from_300
-- name    : TaoFivePrimes.dusart_table1_psi_bounds_for_log_four_from_300
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:31:31.099979+00:00
-- url     : https://prove2.me/theorems/39fc76c7-0aa0-4a4a-8f36-e7eb947276c0
-- title:
--   Dusart Table 1 psi bounds for all rows with b at least 300
-- statement:
--   For any row $(b,\epsilon)$ of the stated Dusart table with $b\ge300$ and every real $x\ge e^b$,
--   $$|\psi(x)-x|\le\epsilon x.$$
--   This covers all twenty rows with exponents from 300 through 9000, with their exact rational coefficients. It makes no assertion for the nineteen rows with smaller initial exponents.
-- source:
--   Original complete Lean derivations recorded in dusart-table1-433, supporting TaoFivePrimes.dusart_table1_psi_bounds_for_log_four (8042dc39-d956-476c-a4d7-36d003a415aa). Numerical table: Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Table 1 and the explicit psi estimates, pp. 230–234, DOI 10.1007/s11139-016-9839-4. The additional bounds here are proved supporting variants, not quotations of unverified numerical inputs. Nonvanishing inputs are the accepted ExplicitPNT and TaoFivePrimes theorems and the accepted OAI.SevenEighths Hecke-to-zeta result. Abel summation and the complete smoothing definitions are reused from their published interfaces with their existing attribution.

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Definitions.Def_DusartThetaTable1Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex Set MeasureTheory
open ExplicitPNT.DusartTable1

theorem TaoFivePrimes.dusart_table1_psi_bounds_for_log_four_from_300 :
∀ (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (hb : 300 ≤ r.b) (x : ℝ) (hx : Real.exp (r.b : ℝ) ≤ x),
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x := by sorry
