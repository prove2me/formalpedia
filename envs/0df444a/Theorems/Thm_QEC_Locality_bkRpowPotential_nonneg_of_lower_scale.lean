-- Prove2me | Theorems.Thm_QEC_Locality_bkRpowPotential_nonneg_of_lower_scale
-- name    : QEC.Locality.bkRpowPotential_nonneg_of_lower_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:37:48.819908+00:00
-- url     : https://prove2.me/theorems/80fcbcd9-7167-41a7-ab1e-bd02143ce419
-- title:
--   Locality: bk Rpow Potential nonneg of lower scale
-- statement:
--   A terminal balanced child has nonnegative source potential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L209-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L209-L226

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkRpowPotential_nonneg_of_lower_scale
    {beta c : ℝ} {d child : Nat}
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hd : 0 < d) (hlower : d ≤ 3 * child) :
    0 ≤ bkRpowPotential beta c d child := by sorry
