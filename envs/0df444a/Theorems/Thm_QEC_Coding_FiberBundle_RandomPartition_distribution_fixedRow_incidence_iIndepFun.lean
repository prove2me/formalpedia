-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_fixedRow_incidence_iIndepFun
-- name    : QEC.Coding.FiberBundle.RandomPartition.distribution_fixedRow_incidence_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:21:10.958216+00:00
-- url     : https://prove2.me/theorems/e08bf93f-bf62-40e1-a7ae-df29810c1e76
-- title:
--   Random Partition: distribution fixed Row incidence i Indep Fun
-- statement:
--   For a fixed check row, all decoded incidence bits remain independent
--   under the full partition sampler.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L212-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L212-L255

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

theorem QEC.Coding.FiberBundle.RandomPartition.distribution_fixedRow_incidence_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (a : Fin (3 * r)) :
    ProbabilityTheory.iIndepFun
      (fun b (sample : Sample r) => sample a b false)
      (distribution r Delta hDelta).toMeasure := by sorry
