-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_delta_mul_four_r_le_xorPairWeight
-- name    : QEC.Coding.FiberBundle.RandomPartition.delta_mul_four_r_le_xorPairWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:42.950487+00:00
-- url     : https://prove2.me/theorems/358f7bc1-3692-43b7-ab89-07db130b157b
-- title:
--   Random Partition: delta mul four r le xor Pair Weight
-- statement:
--   Heavy/light word arithmetic forces all three Fourier characters in the
--   joint two-check identity to have HHO20 scale at least four.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2345-L2387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2345-L2387

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

theorem QEC.Coding.FiberBundle.RandomPartition.delta_mul_four_r_le_xorPairWeight
    (r Delta : Nat)
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r)))
    (hx : 4 * (4 * r) ≤ Delta * HammingWeight x)
    (hOut : Delta * HammingWeight outWord ≤ 2 * (4 * r))
    (hIn : Delta * HammingWeight inWord ≤ 2 * (4 * r)) :
    4 * (4 * r) ≤
      Delta *
        (HammingWeight (x + inWord) +
          HammingWeight (outWord + x)) := by sorry
