-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_product_localPairMean_eq
-- name    : QEC.Coding.FiberBundle.RandomPartition.product_localPairMean_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:19:22.001213+00:00
-- url     : https://prove2.me/theorems/db6bab3c-96b6-4e1b-8bb8-dfa888345ace
-- title:
--   Random Partition: product local Pair Mean eq
-- statement:
--   Closed-form HHO20 `prop:chi` character product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L782-L803
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L782-L803

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

theorem QEC.Coding.FiberBundle.RandomPartition.product_localPairMean_eq
    (r Delta : Nat)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    (∏ b : Fin (4 * r),
        (1 -
          (RandomBase.incidenceProbability (4 * r) Delta).toReal +
          (RandomBase.incidenceProbability (4 * r) Delta).toReal *
            ((RandomBase.paritySign (y b) +
              RandomBase.paritySign (z b)) / 2))) =
      (1 -
        (RandomBase.incidenceProbability (4 * r) Delta).toReal) ^
          HammingWeight (y + z) *
      (1 -
        2 * (RandomBase.incidenceProbability (4 * r) Delta).toReal) ^
          pairOverlapCount y z := by sorry
