-- Prove2me | Theorems.Thm_QEC_Locality_BKRecursivePartition_remainder_card_le_bkSumPreservingRecurrence
-- name    : QEC.Locality.BKRecursivePartition.remainder_card_le_bkSumPreservingRecurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:15:33.822369+00:00
-- url     : https://prove2.me/theorems/12b70c2f-be22-48e5-99c4-ebb5afa1d840
-- title:
--   BKRecursive Partition: remainder card le bk Sum Preserving Recurrence
-- statement:
--   The concrete #380 partition remainder inherits the source-faithful bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L181-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L181-L186

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.BKRecursivePartition.remainder_card_le_bkSumPreservingRecurrence
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) :
    partition.remainder.card ≤ bkSumPreservingRecurrence G d vertices.card := by sorry
