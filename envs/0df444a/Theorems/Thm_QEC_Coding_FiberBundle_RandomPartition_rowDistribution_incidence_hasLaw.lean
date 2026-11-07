-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowDistribution_incidence_hasLaw
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowDistribution_incidence_hasLaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:21:39.82121+00:00
-- url     : https://prove2.me/theorems/c27c0493-73bb-4fc6-98b3-7d072d89bb63
-- title:
--   Random Partition: row Distribution incidence has Law
-- statement:
--   Every incidence projection within one row has exactly the Bernoulli base
--   law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L195-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L195-L208

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowDistribution_incidence_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) :
    ProbabilityTheory.HasLaw
      (fun row : RowSample r => row b false)
      (PMF.bernoulli
        (RandomBase.incidenceProbability (4 * r) Delta)
        (RandomBase.incidenceProbability_le_one hDelta)).toMeasure
      (rowDistribution r Delta hDelta).toMeasure := by sorry
