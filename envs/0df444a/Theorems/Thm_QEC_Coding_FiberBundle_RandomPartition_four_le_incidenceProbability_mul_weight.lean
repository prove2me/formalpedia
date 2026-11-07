-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_four_le_incidenceProbability_mul_weight
-- name    : QEC.Coding.FiberBundle.RandomPartition.four_le_incidenceProbability_mul_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:47.260625+00:00
-- url     : https://prove2.me/theorems/1ca7003b-49aa-4d78-9f7a-ddde6acf3a8d
-- title:
--   Random Partition: four le incidence Probability mul weight
-- statement:
--   Convert an integer-cleared weight threshold into `p * weight ≥ 4`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2390-L2411
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2390-L2411

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

theorem QEC.Coding.FiberBundle.RandomPartition.four_le_incidenceProbability_mul_weight
    (r Delta weight : Nat) (hr : 0 < r)
    (hWeight : 4 * (4 * r) ≤ Delta * weight) :
    (4 : Real) ≤
      (RandomBase.incidenceProbability (4 * r) Delta).toReal *
        weight := by sorry
