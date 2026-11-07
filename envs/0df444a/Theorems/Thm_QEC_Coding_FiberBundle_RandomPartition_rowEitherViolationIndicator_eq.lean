-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowEitherViolationIndicator_eq
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowEitherViolationIndicator_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:31.973195+00:00
-- url     : https://prove2.me/theorems/93b47c7d-49a8-4d78-9f91-f58973034356
-- title:
--   Random Partition: row Either Violation Indicator eq
-- statement:
--   Joint two-check Fourier identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2248-L2284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2248-L2284

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowEitherViolationIndicator_eq
    {r : Nat}
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r)))
    (row : RowSample r) :
    rowEitherViolationIndicator x outWord inWord row =
      (3 -
        RandomBase.paritySign
          (rowPairSyndrome row x outWord) -
        RandomBase.paritySign
          (rowPairSyndrome row inWord x) -
        RandomBase.paritySign
          (rowPairSyndrome row (x + inWord) (outWord + x))) / 4 := by sorry
