-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_card_lightNeighborWord_le
-- name    : QEC.Coding.FiberBundle.RandomPartition.card_lightNeighborWord_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:26:32.8771+00:00
-- url     : https://prove2.me/theorems/9fc23393-fd62-48f1-878c-ae922d004d41
-- title:
--   Random Partition: card light Neighbor Word le
-- statement:
--   Unweighted cardinal bound obtained by clearing the positive geometric
--   test weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3528-L3553
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3528-L3553

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

theorem QEC.Coding.FiberBundle.RandomPartition.card_lightNeighborWord_le
    (r Delta : Nat) (hDelta : 0 < Delta) :
    (Fintype.card (HHO20LightNeighborWord r Delta) : Real) ≤
      (1 + 1 / (Delta : Real)) ^ (4 * r) *
        (Delta : Real) ^ ((8 * r) / Delta) := by sorry
