-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_row_iIndepFun
-- name    : QEC.Coding.FiberBundle.RandomPartition.distribution_row_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:19:09.110434+00:00
-- url     : https://prove2.me/theorems/594bcdcb-2911-4ca6-b287-71d563bd4fd7
-- title:
--   Random Partition: distribution row i Indep Fun
-- statement:
--   The rows of the partitioned-base sampler are mutually independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L121-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L121-L126

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

theorem QEC.Coding.FiberBundle.RandomPartition.distribution_row_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun a (sample : Sample r) => sample a)
      (distribution r Delta hDelta).toMeasure := by sorry
