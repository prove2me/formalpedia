-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_seventyThreeHundredths_mul_card_le_sum_heavyRowMeans
-- name    : QEC.Coding.FiberBundle.RandomPartition.seventyThreeHundredths_mul_card_le_sum_heavyRowMeans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:20:23.582902+00:00
-- url     : https://prove2.me/theorems/b70d380c-b5ab-492a-b22a-cf901c0ccfae
-- title:
--   Random Partition: seventy Three Hundredths mul card le sum heavy Row Means
-- statement:
--   Every selected heavy row has mean at least `.73`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2824-L2864
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2824-L2864

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

theorem QEC.Coding.FiberBundle.RandomPartition.seventyThreeHundredths_mul_card_le_sum_heavyRowMeans
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (types : Finset (Fin typeCount))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (hx : 4 * (4 * r) ≤ Delta * HammingWeight x)
    (hNeighbors :
      ∀ τ ∈ types,
        Delta * HammingWeight (outWord τ) ≤ 2 * (4 * r) ∧
        Delta * HammingWeight (inWord τ) ≤ 2 * (4 * r)) :
    (73 : Real) / 100 *
        (selectedTypeRows r typeCount types).card ≤
      ∑ a ∈ selectedTypeRows r typeCount types,
        ∫ sample,
          sampleRowEitherViolationIndicator
            x outWord inWord a sample ∂
            (distribution r Delta (by omega)).toMeasure := by sorry
