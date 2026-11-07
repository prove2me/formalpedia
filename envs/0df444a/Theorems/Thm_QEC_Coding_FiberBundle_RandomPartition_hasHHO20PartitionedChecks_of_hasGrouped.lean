-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hasHHO20PartitionedChecks_of_hasGrouped
-- name    : QEC.Coding.FiberBundle.RandomPartition.hasHHO20PartitionedChecks_of_hasGrouped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:20:36.879845+00:00
-- url     : https://prove2.me/theorems/9c37aea7-e7e8-4cf1-9586-1039f983c539
-- title:
--   Random Partition: has HHO20 Partitioned Checks of has Grouped
-- statement:
--   Grouped light checks plus deterministic heavy checks are exactly the
--   partitioned-check interface consumed by `TwistGraph.thm_ltc`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L4046-L4058
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L4046-L4058

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

theorem QEC.Coding.FiberBundle.RandomPartition.hasHHO20PartitionedChecks_of_hasGrouped
    {r Delta typeCount ell : Nat} [NeZero typeCount]
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (h :
      HasGroupedHHO20PartitionedChecks
        Delta typeShifts sample) :
    TwistGraph.HasHHO20PartitionedChecks Delta
      (baseSample sample) (twistSample sample typeShifts) := by sorry
