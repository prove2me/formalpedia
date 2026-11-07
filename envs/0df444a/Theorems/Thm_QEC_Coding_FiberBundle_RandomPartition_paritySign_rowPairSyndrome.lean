-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_paritySign_rowPairSyndrome
-- name    : QEC.Coding.FiberBundle.RandomPartition.paritySign_rowPairSyndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:21:29.317351+00:00
-- url     : https://prove2.me/theorems/01a46f74-aba8-4c4d-9d5e-16ac886f15b1
-- title:
--   Random Partition: parity Sign row Pair Syndrome
-- statement:
--   The parity character of a whole row factors over variables.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L437-L457
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L437-L457

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

theorem QEC.Coding.FiberBundle.RandomPartition.paritySign_rowPairSyndrome
    {r : Nat}
    (row : RowSample r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    RandomBase.paritySign (rowPairSyndrome row y z) =
      ∏ b : Fin (4 * r), localPairSign y z b (row b) := by sorry
