-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_sum_selectedTypeRows_eq_sum_typeRows
-- name    : QEC.Coding.FiberBundle.RandomPartition.sum_selectedTypeRows_eq_sum_typeRows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:29.315451+00:00
-- url     : https://prove2.me/theorems/e0aa07c5-a0ee-4aa7-b169-0d35a810b6e6
-- title:
--   Random Partition: sum selected Type Rows eq sum type Rows
-- statement:
--   Fiberwise decomposition of a sum over selected cyclic types.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2811-L2821
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2811-L2821

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

theorem QEC.Coding.FiberBundle.RandomPartition.sum_selectedTypeRows_eq_sum_typeRows
    {r typeCount : Nat} [NeZero typeCount]
    (types : Finset (Fin typeCount))
    (f : Fin (3 * r) → Real) :
    (∑ a ∈ selectedTypeRows r typeCount types, f a) =
      ∑ τ ∈ types, ∑ a ∈ typeRows r typeCount τ, f a := by sorry
