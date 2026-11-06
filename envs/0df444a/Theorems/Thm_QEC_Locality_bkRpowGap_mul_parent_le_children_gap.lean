-- Prove2me | Theorems.Thm_QEC_Locality_bkRpowGap_mul_parent_le_children_gap
-- name    : QEC.Locality.bkRpowGap_mul_parent_le_children_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:37:38.043206+00:00
-- url     : https://prove2.me/theorems/9d19fb0f-9d18-496c-a919-ee2b8daacf78
-- title:
--   Locality: bk Rpow Gap mul parent le children gap
-- statement:
--   Scaling the complementary-child gap from unit mass to an arbitrary positive parent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L112-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L112-L141

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

theorem QEC.Locality.bkRpowGap_mul_parent_le_children_gap
    {c parent left right : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hparent : 0 < parent) (hsum : left + right = parent)
    (hleftLower : parent / 3 ≤ left) (hleftUpper : left ≤ 2 * parent / 3) :
    bkRpowGap c * parent ^ c ≤ left ^ c + right ^ c - parent ^ c := by sorry
