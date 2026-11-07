-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_light_geometric_union_lt_half_of_exp_lt
-- name    : QEC.Coding.FiberBundle.RandomPartition.light_geometric_union_lt_half_of_exp_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:26:27.806648+00:00
-- url     : https://prove2.me/theorems/dac774e5-9006-4a4d-b2f4-ec552f2e2d21
-- title:
--   Random Partition: light geometric union lt half of exp lt
-- statement:
--   A factor-two strengthening of the light geometric union estimate, used
--   to reserve the other half of the probability budget for heavy checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3815-L3877
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3815-L3877

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

theorem QEC.Coding.FiberBundle.RandomPartition.light_geometric_union_lt_half_of_exp_lt
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r)
    (hExpSmall :
      Real.exp
          (-(Delta : Real) / (200 * typeCount)) <
        1 / (32 * r * typeCount : Nat)) :
    (typeCount : Real) *
        ((1 +
          Real.exp
            (-(Delta : Real) / (200 * typeCount))) ^
              (8 * r) - 1) < (1 : Real) / 2 := by sorry
