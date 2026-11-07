-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_card_lightNeighborWord_mul_invDelta_pow_le
-- name    : QEC.Coding.FiberBundle.RandomPartition.card_lightNeighborWord_mul_invDelta_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:56.053118+00:00
-- url     : https://prove2.me/theorems/85bedb25-3faa-4001-9c20-e9ba8f35aec4
-- title:
--   Random Partition: card light Neighbor Word mul inv Delta pow le
-- statement:
--   Weighted counting bound for all light neighbor words.  It is an exact
--   finite analogue of the paper's binary-entropy estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3478-L3524
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3478-L3524

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

theorem QEC.Coding.FiberBundle.RandomPartition.card_lightNeighborWord_mul_invDelta_pow_le
    (r Delta : Nat) (hDelta : 0 < Delta) :
    (Fintype.card (HHO20LightNeighborWord r Delta) : Real) *
        (1 / (Delta : Real)) ^ ((8 * r) / Delta) ≤
      (1 + 1 / (Delta : Real)) ^ (4 * r) := by sorry
