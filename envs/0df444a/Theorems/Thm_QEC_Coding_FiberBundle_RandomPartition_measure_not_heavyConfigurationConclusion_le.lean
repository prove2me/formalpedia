-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_not_heavyConfigurationConclusion_le
-- name    : QEC.Coding.FiberBundle.RandomPartition.measure_not_heavyConfigurationConclusion_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:34.576195+00:00
-- url     : https://prove2.me/theorems/a785e1f1-934b-4797-8036-e8b7efb644bc
-- title:
--   Random Partition: measure not heavy Configuration Conclusion le
-- statement:
--   For a fixed admissible heavy configuration, failure of the deterministic
--   HHO20 heavy-check conclusion has probability at most `exp(-3r)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3215-L3288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3215-L3288

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

theorem QEC.Coding.FiberBundle.RandomPartition.measure_not_heavyConfigurationConclusion_le
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (x : Word (ZMod 2) (Fin (4 * r)))
    (types : Finset (Fin typeCount))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (hx : 4 * (4 * r) ≤ Delta * HammingWeight x)
    (hTypes : 98 * typeCount ≤ 100 * types.card)
    (hNeighbors :
      ∀ τ ∈ types,
        Delta * HammingWeight (outWord τ) ≤ 2 * (4 * r) ∧
        Delta * HammingWeight (inWord τ) ≤ 2 * (4 * r)) :
    (distribution r Delta (by omega)).toMeasure.real
        {sample |
          ¬4 * r ≤
            100 *
              TwistGraph.heavyIncidentViolationCount
                (baseSample sample) (twistSample sample typeShifts)
                x types outWord inWord} ≤
      Real.exp (-3 * (r : Real)) := by sorry
