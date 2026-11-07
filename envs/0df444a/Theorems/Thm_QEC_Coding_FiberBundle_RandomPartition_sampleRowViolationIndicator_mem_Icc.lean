-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_sampleRowViolationIndicator_mem_Icc
-- name    : QEC.Coding.FiberBundle.RandomPartition.sampleRowViolationIndicator_mem_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:22:48.610247+00:00
-- url     : https://prove2.me/theorems/f19e9f25-7212-47ef-8cdc-5e15a0cd11c0
-- title:
--   Random Partition: sample Row Violation Indicator mem Icc
-- statement:
--   Each full-sample row indicator lies in `[0,1]`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1078-L1085
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1078-L1085

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

theorem QEC.Coding.FiberBundle.RandomPartition.sampleRowViolationIndicator_mem_Icc
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r))
    (sample : Sample r) :
    sampleRowViolationIndicator y z a sample ∈ Set.Icc (0 : Real) 1 := by sorry
