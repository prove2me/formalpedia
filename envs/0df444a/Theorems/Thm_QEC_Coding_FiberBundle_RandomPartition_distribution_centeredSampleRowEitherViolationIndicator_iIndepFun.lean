-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_centeredSampleRowEitherViolationIndicator_iIndepFun
-- name    : QEC.Coding.FiberBundle.RandomPartition.distribution_centeredSampleRowEitherViolationIndicator_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:50.048051+00:00
-- url     : https://prove2.me/theorems/5a55b929-c539-4db1-b3b1-7a5595c20bcc
-- title:
--   Random Partition: distribution centered Sample Row Either Violation Indicator i Indep Fun
-- statement:
--   Centered heavy-row indicators remain mutually independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2739-L2759
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2739-L2759

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

theorem QEC.Coding.FiberBundle.RandomPartition.distribution_centeredSampleRowEitherViolationIndicator_iIndepFun
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : Delta ≤ 4 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r))) :
    ProbabilityTheory.iIndepFun
      (fun a =>
        centeredSampleRowEitherViolationIndicator
          Delta hDelta x outWord inWord a)
      (distribution r Delta hDelta).toMeasure := by sorry
