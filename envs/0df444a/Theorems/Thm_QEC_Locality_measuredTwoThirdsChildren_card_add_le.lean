-- Prove2me | Theorems.Thm_QEC_Locality_measuredTwoThirdsChildren_card_add_le
-- name    : QEC.Locality.measuredTwoThirdsChildren_card_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:36:42.421164+00:00
-- url     : https://prove2.me/theorems/8a44607b-0bc8-4d02-b584-6cfce4e00a1b
-- title:
--   Locality: measured Two Thirds Children card add le
-- statement:
--   The actual measured children from #380 preserve their parent cardinality sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L91-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L91-L108

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.measuredTwoThirdsChildren_card_add_le
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    (measuredTwoThirdsLeft G vertices).card +
        (measuredTwoThirdsRight G vertices).card ≤ vertices.card := by sorry
