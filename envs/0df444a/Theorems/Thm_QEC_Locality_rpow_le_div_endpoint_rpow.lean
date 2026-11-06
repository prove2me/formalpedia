-- Prove2me | Theorems.Thm_QEC_Locality_rpow_le_div_endpoint_rpow
-- name    : QEC.Locality.rpow_le_div_endpoint_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:15:47.870292+00:00
-- url     : https://prove2.me/theorems/0a19bcdc-27db-42dc-b318-7b9b3e311124
-- title:
--   Locality: rpow le div endpoint rpow
-- statement:
--   On `[a,1]`, a sublinear power is bounded by its endpoint-scaled chord.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L178-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L178-L194

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

theorem QEC.Locality.rpow_le_div_endpoint_rpow
    {a q c : ℝ} (ha : 0 < a) (haq : a ≤ q)
    (hc1 : c < 1) :
    q ^ c ≤ q / a ^ (1 - c) := by sorry
