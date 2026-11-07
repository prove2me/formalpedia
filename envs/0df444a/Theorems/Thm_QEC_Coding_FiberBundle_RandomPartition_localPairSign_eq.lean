-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_localPairSign_eq
-- name    : QEC.Coding.FiberBundle.RandomPartition.localPairSign_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:21:40.977293+00:00
-- url     : https://prove2.me/theorems/77ee64e8-d3d1-4988-abc0-4506062916cf
-- title:
--   Random Partition: local Pair Sign eq
-- statement:
--   Algebraic decomposition of a local parity character into its incidence
--   and head/tail factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L477-L489
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L477-L489

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

theorem QEC.Coding.FiberBundle.RandomPartition.localPairSign_eq
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r))
    (localSample : LocalSample) :
    localPairSign y z b localSample =
      1 - localIncidenceReal localSample +
        localIncidenceReal localSample *
          localSelectedPairSign y z b localSample := by sorry
