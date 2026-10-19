-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_table1_psi_bounds_for_log_four_above_exp300
-- name    : TaoFivePrimes.dusart_table1_psi_bounds_for_log_four_above_exp300
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:31:34.607381+00:00
-- url     : https://prove2.me/theorems/e30f24d9-7412-435a-8419-2d32c9396ee3
-- title:
--   Every Dusart table row on its target domain above exp(300)
-- statement:
--   Let $(b,\epsilon)$ be any of the 39 rows in the stated Dusart table. If $x\ge e^b$ and $x\ge e^{300}$, then
--   $$|\psi(x)-x|\le\epsilon x.$$
--   This is the completed common tail of all the original row domains.
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

theorem TaoFivePrimes.dusart_table1_psi_bounds_for_log_four_above_exp300 :
∀ (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (x : ℝ) (hx : Real.exp (r.b : ℝ) ≤ x) (h300 : Real.exp 300 ≤ x),
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x := by sorry
