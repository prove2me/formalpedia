-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_centeredSampleRowViolationIndicator_iIndepFun
-- name    : QEC.Coding.FiberBundle.RandomPartition.distribution_centeredSampleRowViolationIndicator_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:23:29.865312+00:00
-- url     : https://prove2.me/theorems/6c32f552-134b-4327-9c40-4a04644e23c0
-- title:
--   Random Partition: distribution centered Sample Row Violation Indicator i Indep Fun
-- statement:
--   Centering by the common deterministic row mean preserves mutual
--   independence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1347-L1361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1347-L1361

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

theorem QEC.Coding.FiberBundle.RandomPartition.distribution_centeredSampleRowViolationIndicator_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    ProbabilityTheory.iIndepFun
      (fun a =>
        centeredSampleRowViolationIndicator Delta hDelta y z a)
      (distribution r Delta hDelta).toMeasure := by sorry
