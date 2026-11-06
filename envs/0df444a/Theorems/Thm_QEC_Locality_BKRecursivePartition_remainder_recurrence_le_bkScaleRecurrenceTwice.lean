-- Prove2me | Theorems.Thm_QEC_Locality_BKRecursivePartition_remainder_recurrence_le_bkScaleRecurrenceTwice
-- name    : QEC.Locality.BKRecursivePartition.remainder_recurrence_le_bkScaleRecurrenceTwice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:14:10.343524+00:00
-- url     : https://prove2.me/theorems/3e94ffdb-59cf-44c2-9447-f543599b8069
-- title:
--   BKRecursive Partition: remainder recurrence le bk Scale Recurrence Twice
-- statement:
--   After one partition below scale `r`, the recursive charge of its remainder is
--   bounded by the source-scale composition `S_d(S_d(r))` for the second pass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L537-L544
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L537-L544

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.BKRecursivePartition.remainder_recurrence_le_bkScaleRecurrenceTwice
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) (r : Nat)
    (hvertices : vertices.card ≤ r) :
    bkSeparatorRecurrence G d partition.remainder ≤ bkScaleRecurrenceTwice G d r := by sorry
