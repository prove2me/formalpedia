-- Prove2me | Theorems.Thm_QEC_Locality_neg_mul_log_mul_one_sub_le_rpow_sub
-- name    : QEC.Locality.neg_mul_log_mul_one_sub_le_rpow_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:37:48.529734+00:00
-- url     : https://prove2.me/theorems/eef82e57-730f-4a6c-a682-7976b5dc0308
-- title:
--   Locality: neg mul log mul one sub le rpow sub
-- statement:
--   Tangent-line lower bound for a fixed-base real power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L152-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L152-L165

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

theorem QEC.Locality.neg_mul_log_mul_one_sub_le_rpow_sub
    {base c : ℝ} (hbase : 0 < base) :
    -base * Real.log base * (1 - c) ≤ base ^ c - base := by sorry
