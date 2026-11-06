-- Prove2me | Theorems.Thm_QEC_Locality_bkEntropyGap_mul_one_sub_le_bkRpowGap
-- name    : QEC.Locality.bkEntropyGap_mul_one_sub_le_bkRpowGap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:37:33.786683+00:00
-- url     : https://prove2.me/theorems/8a435a70-4fad-49b3-b7ef-5fa002074769
-- title:
--   Locality: bk Entropy Gap mul one sub le bk Rpow Gap
-- statement:
--   The exact gap dominates its first-order entropy lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L168-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L168-L175

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

theorem QEC.Locality.bkEntropyGap_mul_one_sub_le_bkRpowGap (c : ℝ) :
    bkEntropyGap * (1 - c) ≤ bkRpowGap c := by sorry
