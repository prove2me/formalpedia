-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_card_selectedTypeRows_of_dvd
-- name    : QEC.Coding.FiberBundle.RandomPartition.card_selectedTypeRows_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:19:07.691631+00:00
-- url     : https://prove2.me/theorems/e7caccf1-93d5-40f7-9484-937c6f55db1f
-- title:
--   Random Partition: card selected Type Rows of dvd
-- statement:
--   Exact size of a union of cyclic type fibers under the divisibility
--   condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2544-L2599
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2544-L2599

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

theorem QEC.Coding.FiberBundle.RandomPartition.card_selectedTypeRows_of_dvd
    (r typeCount : Nat) [NeZero typeCount]
    (hTypeDvd : typeCount ∣ 3 * r)
    (types : Finset (Fin typeCount)) :
    (selectedTypeRows r typeCount types).card =
      types.card * ((3 * r) / typeCount) := by sorry
