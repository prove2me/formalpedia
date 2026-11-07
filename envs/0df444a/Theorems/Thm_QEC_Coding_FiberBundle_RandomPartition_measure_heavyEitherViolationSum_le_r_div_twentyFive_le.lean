-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_heavyEitherViolationSum_le_r_div_twentyFive_le
-- name    : QEC.Coding.FiberBundle.RandomPartition.measure_heavyEitherViolationSum_le_r_div_twentyFive_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:36.828257+00:00
-- url     : https://prove2.me/theorems/2dc26984-0e1d-4471-a6e9-86acb087c8ac
-- title:
--   Random Partition: measure heavy Either Violation Sum le r div twenty Five le
-- statement:
--   Fixed heavy configuration at the actual HHO20 `.01n = .04r`
--   threshold.  Keeping the exact 98-percent row count sharpens the Hoeffding
--   exponent to at least `3r`, which is strong enough to beat the `2^(4r)`
--   choices of the central word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3108-L3211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3108-L3211

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

theorem QEC.Coding.FiberBundle.RandomPartition.measure_heavyEitherViolationSum_le_r_div_twentyFive_le
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
            (r : Real) / 25} ≤
      Real.exp (-3 * (r : Real)) := by sorry
