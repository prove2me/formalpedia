-- Prove2me | Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_le_bkSumPreservingRecurrence_card
-- name    : QEC.Locality.bkSeparatorRecurrence_le_bkSumPreservingRecurrence_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:06:25.097284+00:00
-- url     : https://prove2.me/theorems/ead7f13d-c221-4bd7-b76d-9f318756001c
-- title:
--   Locality: bk Separator Recurrence le bk Sum Preserving Recurrence card
-- statement:
--   The concrete measured separator charge from #380 is controlled by the
--   sum-preserving scale recurrence at its exact parent cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L128-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L128-L178

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkSeparatorRecurrence_le_bkSumPreservingRecurrence_card
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι) :
    bkSeparatorRecurrence G d vertices ≤
      bkSumPreservingRecurrence G d vertices.card := by sorry
