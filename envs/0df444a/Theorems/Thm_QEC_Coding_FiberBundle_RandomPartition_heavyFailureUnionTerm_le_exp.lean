-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_heavyFailureUnionTerm_le_exp
-- name    : QEC.Coding.FiberBundle.RandomPartition.heavyFailureUnionTerm_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:26:31.222367+00:00
-- url     : https://prove2.me/theorems/ce996052-831d-49bc-a118-69fa6ba80be6
-- title:
--   Random Partition: heavy Failure Union Term le exp
-- statement:
--   The heavy union term is bounded by one explicit exponential exponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3616-L3673
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3616-L3673

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

theorem QEC.Coding.FiberBundle.RandomPartition.heavyFailureUnionTerm_le_exp
    (r Delta typeCount : Nat) (hDelta : 0 < Delta) :
    (Fintype.card (HeavyFailureIndex r Delta typeCount) : Real) *
        Real.exp (-3 * (r : Real)) ≤
      Real.exp
        ((((4 * r + typeCount : Nat) : Real) * Real.log 2) +
          ((2 * typeCount : Nat) : Real) *
            ((((4 * r : Nat) : Real) / Delta) +
              (((8 * r) / Delta : Nat) : Real) * Real.log Delta) -
          3 * (r : Real)) := by sorry
