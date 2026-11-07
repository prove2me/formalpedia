-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_incidence_hasLaw
-- name    : QEC.Coding.FiberBundle.RandomPartition.distribution_incidence_hasLaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:21:13.898194+00:00
-- url     : https://prove2.me/theorems/1fe3dbc7-c497-413f-9132-20d86239d02d
-- title:
--   Random Partition: distribution incidence has Law
-- statement:
--   Every decoded Tanner incidence has exactly the Bernoulli base law under
--   the full partition sampler.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L279-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L279-L295

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

theorem QEC.Coding.FiberBundle.RandomPartition.distribution_incidence_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (edge : Fin (3 * r) × Fin (4 * r)) :
    ProbabilityTheory.HasLaw
      (fun sample : Sample r => sample edge.1 edge.2 false)
      (PMF.bernoulli
        (RandomBase.incidenceProbability (4 * r) Delta)
        (RandomBase.incidenceProbability_le_one hDelta)).toMeasure
      (distribution r Delta hDelta).toMeasure := by sorry
