-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_mgf_sampleRowViolationIndicator
-- name    : QEC.Coding.FiberBundle.RandomPartition.mgf_sampleRowViolationIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:22:58.677588+00:00
-- url     : https://prove2.me/theorems/48191ecc-35c1-4b5d-861b-ff9445f3b0fd
-- title:
--   Random Partition: mgf sample Row Violation Indicator
-- statement:
--   Exact moment-generating function of one Bernoulli row-violation
--   indicator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1137-L1174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1137-L1174

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

theorem QEC.Coding.FiberBundle.RandomPartition.mgf_sampleRowViolationIndicator
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) (t : Real) :
    ProbabilityTheory.mgf
        (sampleRowViolationIndicator y z a)
        (distribution r Delta hDelta).toMeasure t =
      1 -
        (rowDistribution r Delta hDelta).toMeasure.real
          {row | rowPairSyndrome row y z ≠ 0} +
        (rowDistribution r Delta hDelta).toMeasure.real
          {row | rowPairSyndrome row y z ≠ 0} * Real.exp t := by sorry
