-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hasHHO20LightChecks_of_hasGrouped
-- name    : QEC.Coding.FiberBundle.RandomPartition.hasHHO20LightChecks_of_hasGrouped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:20:24.005001+00:00
-- url     : https://prove2.me/theorems/b54188b9-0776-4175-99fe-f3ef4be88ca5
-- title:
--   Random Partition: has HHO20 Light Checks of has Grouped
-- statement:
--   The grouped light event is exactly strong enough for the deterministic
--   HHO20 light-check interface, independently of the chosen type shifts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2133-L2145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2133-L2145

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

theorem QEC.Coding.FiberBundle.RandomPartition.hasHHO20LightChecks_of_hasGrouped
    {r Delta typeCount ell : Nat} [NeZero typeCount]
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (hGrouped :
      HasGroupedHHO20LightChecks
        (r := r) (typeCount := typeCount) Delta sample) :
    TwistGraph.HasHHO20LightChecks Delta
      (baseSample sample) (twistSample sample typeShifts) := by sorry
