-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowPairSyndrome_add
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowPairSyndrome_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:20.335221+00:00
-- url     : https://prove2.me/theorems/33bcf558-3aaf-408d-b132-fa0f539339d1
-- title:
--   Random Partition: row Pair Syndrome add
-- statement:
--   The sum of the outgoing and incoming paired syndromes is itself the
--   paired syndrome on the two XOR words used in HHO20's heavy argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2193-L2207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2193-L2207

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowPairSyndrome_add
    {r : Nat}
    (row : RowSample r)
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r))) :
    rowPairSyndrome row x outWord +
        rowPairSyndrome row inWord x =
      rowPairSyndrome row (x + inWord) (outWord + x) := by sorry
