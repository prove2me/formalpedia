-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_sum_sampleRowViolationIndicator_typeRows_eq
-- name    : QEC.Coding.FiberBundle.RandomPartition.sum_sampleRowViolationIndicator_typeRows_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:19:48.937757+00:00
-- url     : https://prove2.me/theorems/0c792ddc-1e59-47dd-8b59-d343cb6f3d27
-- title:
--   Random Partition: sum sample Row Violation Indicator type Rows eq
-- statement:
--   Summing grouped row indicators over a type fiber is definitionally the
--   existing deterministic `typeViolationCount`, for every choice of type
--   shifts.  Thus partitioned-check events do not depend on the spectrum
--   randomness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1447-L1469
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1447-L1469

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

theorem QEC.Coding.FiberBundle.RandomPartition.sum_sampleRowViolationIndicator_typeRows_eq
    {r typeCount ell : Nat} [NeZero typeCount]
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    (∑ a ∈ typeRows r typeCount τ,
        sampleRowViolationIndicator y z a sample) =
      (TwistGraph.typeViolationCount
        (baseSample sample) (twistSample sample typeShifts)
        τ y z : Real) := by sorry
