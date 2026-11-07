-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_not_isFullyGood_baseSample_le
-- name    : QEC.Coding.FiberBundle.RandomPartition.measure_not_isFullyGood_baseSample_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:21:16.593876+00:00
-- url     : https://prove2.me/theorems/e84eef6c-2a0b-4ff3-a2a3-19480b43d93e
-- title:
--   Random Partition: measure not is Fully Good base Sample le
-- statement:
--   The Random Partition construction uses the measure not is Fully Good base Sample le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L365-L386
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L365-L386

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
set_option maxHeartbeats 800000

theorem QEC.Coding.FiberBundle.RandomPartition.measure_not_isFullyGood_baseSample_le
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r) :
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          ¬RandomBase.IsFullyGood
            (Delta := Delta) (baseSample sample)} ≤
      (fullyGoodBaseFailureBound r Delta).toReal := by sorry
