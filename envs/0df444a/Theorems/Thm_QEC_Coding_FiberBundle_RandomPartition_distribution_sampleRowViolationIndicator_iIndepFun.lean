-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_sampleRowViolationIndicator_iIndepFun
-- name    : QEC.Coding.FiberBundle.RandomPartition.distribution_sampleRowViolationIndicator_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:19:54.188691+00:00
-- url     : https://prove2.me/theorems/333109e7-cf0c-4ae0-98ac-c742f6080f90
-- title:
--   Random Partition: distribution sample Row Violation Indicator i Indep Fun
-- statement:
--   Row-violation indicators are mutually independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1125-L1133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1125-L1133

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

theorem QEC.Coding.FiberBundle.RandomPartition.distribution_sampleRowViolationIndicator_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    ProbabilityTheory.iIndepFun
      (fun a => sampleRowViolationIndicator y z a)
      (distribution r Delta hDelta).toMeasure := by sorry
