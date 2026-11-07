-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_heavyEitherViolationSum_le_oneFifth_le
-- name    : QEC.Coding.FiberBundle.RandomPartition.measure_heavyEitherViolationSum_le_oneFifth_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:36:54.735583+00:00
-- url     : https://prove2.me/theorems/1e3c5d2d-bdd8-4b80-a49c-6dc64a9a4ff5
-- title:
--   Random Partition: measure heavy Either Violation Sum le one Fifth le
-- statement:
--   Fixed heavy configuration: fewer than one fifth of selected rows with
--   an outgoing-or-incoming violation has probability at most
--   `exp(-selectedRows/2)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2893-L2998
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2893-L2998

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

theorem QEC.Coding.FiberBundle.RandomPartition.measure_heavyEitherViolationSum_le_oneFifth_le
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
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
    let rows := selectedTypeRows r typeCount types
    (distribution r Delta (by omega)).toMeasure.real
        {sample |
          (∑ a ∈ rows,
            sampleRowEitherViolationIndicator
              x outWord inWord a sample) ≤
            (rows.card : Real) / 5} ≤
      Real.exp (-(rows.card : Real) / 2) := by sorry
