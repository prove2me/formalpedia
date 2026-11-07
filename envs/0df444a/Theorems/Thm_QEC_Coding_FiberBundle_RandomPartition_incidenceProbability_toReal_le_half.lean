-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_incidenceProbability_toReal_le_half
-- name    : QEC.Coding.FiberBundle.RandomPartition.incidenceProbability_toReal_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:19:17.951309+00:00
-- url     : https://prove2.me/theorems/0a19f9ee-5b25-4431-8eb6-a9a3068cee6d
-- title:
--   Random Partition: incidence Probability to Real le half
-- statement:
--   The HHO20 parameter condition `Delta ≤ 2r` puts the sampled incidence
--   density below one half, including the degenerate `r = 0` case.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L910-L926
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L910-L926

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

theorem QEC.Coding.FiberBundle.RandomPartition.incidenceProbability_toReal_le_half
    (r Delta : Nat) (hDeltaHalf : Delta ≤ 2 * r) :
    (RandomBase.incidenceProbability (4 * r) Delta).toReal ≤
      (1 : Real) / 2 := by sorry
