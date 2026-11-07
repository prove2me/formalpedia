-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_groupedTypeViolationCount_eq_typeViolationCount
-- name    : QEC.Coding.FiberBundle.RandomPartition.groupedTypeViolationCount_eq_typeViolationCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:01.022737+00:00
-- url     : https://prove2.me/theorems/f051562b-e299-46c8-a5aa-4c28407fd227
-- title:
--   Random Partition: grouped Type Violation Count eq type Violation Count
-- statement:
--   Natural-number version of the bridge to deterministic
--   `typeViolationCount`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1473-L1487
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1473-L1487

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

theorem QEC.Coding.FiberBundle.RandomPartition.groupedTypeViolationCount_eq_typeViolationCount
    {r typeCount ell : Nat} [NeZero typeCount]
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    groupedTypeViolationCount sample τ y z =
      TwistGraph.typeViolationCount
        (baseSample sample) (twistSample sample typeShifts)
        τ y z := by sorry
