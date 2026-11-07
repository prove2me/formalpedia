-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_heavyFailureUnionTerm_le_exp_neg_tenth
-- name    : QEC.Coding.FiberBundle.RandomPartition.heavyFailureUnionTerm_le_exp_neg_tenth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:26:36.759193+00:00
-- url     : https://prove2.me/theorems/211f474b-dcba-4c0d-81a5-ead6ff0d2e15
-- title:
--   Random Partition: heavy Failure Union Term le exp neg tenth
-- statement:
--   Paper-natural scale conditions make the full heavy union exponentially
--   small, with a concrete remaining exponent `r/10`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3677-L3768
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3677-L3768

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

theorem QEC.Coding.FiberBundle.RandomPartition.heavyFailureUnionTerm_le_exp_neg_tenth
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall :
      (100 : Real) * typeCount ≤ r)
    (hScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta) :
    (Fintype.card (HeavyFailureIndex r Delta typeCount) : Real) *
        Real.exp (-3 * (r : Real)) ≤
      Real.exp (-(r : Real) / 10) := by sorry
