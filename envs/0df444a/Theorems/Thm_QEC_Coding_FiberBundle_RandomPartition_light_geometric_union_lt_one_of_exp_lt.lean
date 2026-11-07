-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_light_geometric_union_lt_one_of_exp_lt
-- name    : QEC.Coding.FiberBundle.RandomPartition.light_geometric_union_lt_one_of_exp_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:20:09.017198+00:00
-- url     : https://prove2.me/theorems/9701f709-117c-491e-83be-c31513d2ea96
-- title:
--   Random Partition: light geometric union lt one of exp lt
-- statement:
--   A simple scale condition on the one-coordinate geometric factor
--   discharges the simultaneous light-event union bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1997-L2059
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1997-L2059

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

theorem QEC.Coding.FiberBundle.RandomPartition.light_geometric_union_lt_one_of_exp_lt
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r)
    (hExpSmall :
      Real.exp
          (-(Delta : Real) / (200 * typeCount)) <
        1 / (16 * r * typeCount : Nat)) :
    (typeCount : Real) *
        ((1 +
          Real.exp
            (-(Delta : Real) / (200 * typeCount))) ^
              (8 * r) - 1) < 1 := by sorry
