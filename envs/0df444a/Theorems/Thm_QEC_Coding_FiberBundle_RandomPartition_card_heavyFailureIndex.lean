-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_card_heavyFailureIndex
-- name    : QEC.Coding.FiberBundle.RandomPartition.card_heavyFailureIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:52.87258+00:00
-- url     : https://prove2.me/theorems/7454e88d-a0ee-42e8-9085-fe53612c88bd
-- title:
--   Random Partition: card heavy Failure Index
-- statement:
--   Exact product count for the finite heavy-configuration index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3467-L3474
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3467-L3474

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomPartition.card_heavyFailureIndex
    (r Delta typeCount : Nat) :
    Fintype.card (HeavyFailureIndex r Delta typeCount) =
      2 ^ (4 * r) *
        (2 ^ typeCount *
          (Fintype.card (HHO20LightNeighborWord r Delta) ^ typeCount *
            Fintype.card (HHO20LightNeighborWord r Delta) ^ typeCount)) := by sorry
