-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_lightNeighborCardEnvelope_le_exp
-- name    : QEC.Coding.FiberBundle.RandomPartition.lightNeighborCardEnvelope_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:26:20.609198+00:00
-- url     : https://prove2.me/theorems/a557202e-c7a1-4439-abfc-2e99bde4535a
-- title:
--   Random Partition: light Neighbor Card Envelope le exp
-- statement:
--   The elementary exponential envelope for the weighted light-neighbor
--   count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3582-L3613
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3582-L3613

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

theorem QEC.Coding.FiberBundle.RandomPartition.lightNeighborCardEnvelope_le_exp
    (r Delta : Nat) (hDelta : 0 < Delta) :
    (1 + 1 / (Delta : Real)) ^ (4 * r) *
        (Delta : Real) ^ ((8 * r) / Delta) ≤
      Real.exp
        (((4 * r : Nat) : Real) / Delta +
          (((8 * r) / Delta : Nat) : Real) * Real.log Delta) := by sorry
