-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_selectedTypeRows_card_bounds
-- name    : QEC.Coding.FiberBundle.RandomPartition.selectedTypeRows_card_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:40.977022+00:00
-- url     : https://prove2.me/theorems/b4aff3bc-aad8-4335-983c-7d96f53cf378
-- title:
--   Random Partition: selected Type Rows card bounds
-- statement:
--   Exact integer-scaled bounds recording that at least 98 percent of the
--   three-quarters-rate check rows are selected.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3085-L3102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3085-L3102

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

theorem QEC.Coding.FiberBundle.RandomPartition.selectedTypeRows_card_bounds
    (r typeCount : Nat) [NeZero typeCount]
    (hTypeDvd : typeCount ∣ 3 * r)
    (types : Finset (Fin typeCount))
    (hTypes : 98 * typeCount ≤ 100 * types.card) :
    294 * r ≤
        100 * (selectedTypeRows r typeCount types).card ∧
      (selectedTypeRows r typeCount types).card ≤ 3 * r := by sorry
