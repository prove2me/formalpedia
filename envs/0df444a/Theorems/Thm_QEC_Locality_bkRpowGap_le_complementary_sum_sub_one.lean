-- Prove2me | Theorems.Thm_QEC_Locality_bkRpowGap_le_complementary_sum_sub_one
-- name    : QEC.Locality.bkRpowGap_le_complementary_sum_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:37:09.441486+00:00
-- url     : https://prove2.me/theorems/62a836a8-a197-442c-85b6-daeb389c7097
-- title:
--   Locality: bk Rpow Gap le complementary sum sub one
-- statement:
--   Endpoint lower bound for complementary powers on the balanced interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L69-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L69-L97

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

theorem QEC.Locality.bkRpowGap_le_complementary_sum_sub_one
    {c t : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (ht : t ∈ Set.Icc (1 / 3 : ℝ) (2 / 3 : ℝ)) :
    bkRpowGap c ≤ t ^ c + (1 - t) ^ c - 1 := by sorry
