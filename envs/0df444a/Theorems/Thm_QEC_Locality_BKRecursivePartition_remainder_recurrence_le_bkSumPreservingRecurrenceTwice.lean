-- Prove2me | Theorems.Thm_QEC_Locality_BKRecursivePartition_remainder_recurrence_le_bkSumPreservingRecurrenceTwice
-- name    : QEC.Locality.BKRecursivePartition.remainder_recurrence_le_bkSumPreservingRecurrenceTwice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:26:04.189375+00:00
-- url     : https://prove2.me/theorems/d7c38c66-490f-4c4b-a17e-9ace5eb5dd63
-- title:
--   BKRecursive Partition: remainder recurrence le bk Sum Preserving Recurrence Twice
-- statement:
--   The second concrete #380 charge is controlled by the sum-preserving composition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L245-L253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L245-L253

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.BKRecursivePartition.remainder_recurrence_le_bkSumPreservingRecurrenceTwice
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) :
    bkSeparatorRecurrence G d partition.remainder ≤
      bkSumPreservingRecurrenceTwice G d vertices.card := by sorry
