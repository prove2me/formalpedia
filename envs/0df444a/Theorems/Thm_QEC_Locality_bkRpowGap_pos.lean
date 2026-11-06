-- Prove2me | Theorems.Thm_QEC_Locality_bkRpowGap_pos
-- name    : QEC.Locality.bkRpowGap_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:07:30.221372+00:00
-- url     : https://prove2.me/theorems/209a61cd-7595-4fb3-a2c0-fd572510da60
-- title:
--   Locality: bk Rpow Gap pos
-- statement:
--   The balanced `rpow` gap is strictly positive for every exponent below one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L100-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L100-L109

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

theorem QEC.Locality.bkRpowGap_pos {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 < bkRpowGap c := by sorry
