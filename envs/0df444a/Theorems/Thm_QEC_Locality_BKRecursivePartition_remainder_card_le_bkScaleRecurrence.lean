-- Prove2me | Theorems.Thm_QEC_Locality_BKRecursivePartition_remainder_card_le_bkScaleRecurrence
-- name    : QEC.Locality.BKRecursivePartition.remainder_card_le_bkScaleRecurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:33:57.705197+00:00
-- url     : https://prove2.me/theorems/6575dffc-22c8-4058-b572-4383ba58353b
-- title:
--   BKRecursive Partition: remainder card le bk Scale Recurrence
-- statement:
--   The BKRecursive Partition construction uses the remainder card le bk Scale Recurrence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L525-L531
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L525-L531

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

theorem QEC.Locality.BKRecursivePartition.remainder_card_le_bkScaleRecurrence
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) (r : Nat)
    (hvertices : vertices.card ≤ r) :
    partition.remainder.card ≤ bkScaleRecurrence G d r := by sorry
