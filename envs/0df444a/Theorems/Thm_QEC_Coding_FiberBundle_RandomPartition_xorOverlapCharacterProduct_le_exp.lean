-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_xorOverlapCharacterProduct_le_exp
-- name    : QEC.Coding.FiberBundle.RandomPartition.xorOverlapCharacterProduct_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:19:26.41157+00:00
-- url     : https://prove2.me/theorems/1b0b7e3e-7e8c-4d11-befd-1e5ba46b770d
-- title:
--   Random Partition: xor Overlap Character Product le exp
-- statement:
--   The exact XOR/overlap character product is bounded by the exponential
--   envelope used in HHO20.  This analytic lemma is stated for an abstract
--   incidence density so that every numerical side condition is explicit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L873-L906
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L873-L906

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

theorem QEC.Coding.FiberBundle.RandomPartition.xorOverlapCharacterProduct_le_exp
    (p : Real) (xorWeight overlap : Nat)
    (hpHalf : p ≤ 1 / 2) :
    (1 - p) ^ xorWeight * (1 - 2 * p) ^ overlap ≤
      Real.exp
        (-p * ((xorWeight : Real) + 2 * (overlap : Real))) := by sorry
