-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowEitherViolationIndicator_le_add
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowEitherViolationIndicator_le_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:30.865217+00:00
-- url     : https://prove2.me/theorems/b72a5165-3614-4a71-94f3-774554ebc937
-- title:
--   Random Partition: row Either Violation Indicator le add
-- statement:
--   An OR-violation indicator is bounded by the sum of its two constituent
--   check indicators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3002-L3015
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3002-L3015

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowEitherViolationIndicator_le_add
    {r : Nat}
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r)))
    (row : RowSample r) :
    rowEitherViolationIndicator x outWord inWord row ≤
      rowViolationIndicator x outWord row +
        rowViolationIndicator inWord x row := by sorry
