-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exp_neg_delta_div_lt_of_log_scale
-- name    : QEC.Coding.FiberBundle.RandomPartition.exp_neg_delta_div_lt_of_log_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:20:14.193192+00:00
-- url     : https://prove2.me/theorems/2e820247-8ac5-4fb5-85e1-dcb8a8a85929
-- title:
--   Random Partition: exp neg delta div lt of log scale
-- statement:
--   A logarithmic HHO20 scale inequality implies the exponential smallness
--   condition used by the light-event union bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2063-L2093
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2063-L2093

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

theorem QEC.Coding.FiberBundle.RandomPartition.exp_neg_delta_div_lt_of_log_scale
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r)
    (hLogScale :
      200 * (typeCount : Real) *
          Real.log (16 * r * typeCount : Nat) <
        Delta) :
    Real.exp
        (-(Delta : Real) / (200 * typeCount)) <
      1 / (16 * r * typeCount : Nat) := by sorry
