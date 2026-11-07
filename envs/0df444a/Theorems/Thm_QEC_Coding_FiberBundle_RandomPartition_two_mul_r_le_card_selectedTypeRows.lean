-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_two_mul_r_le_card_selectedTypeRows
-- name    : QEC.Coding.FiberBundle.RandomPartition.two_mul_r_le_card_selectedTypeRows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:37:33.029207+00:00
-- url     : https://prove2.me/theorems/33066a5c-44b2-448e-857a-c59f670cb664
-- title:
--   Random Partition: two mul r le card selected Type Rows
-- statement:
--   Selecting at least 98 percent of the types selects at least `2r` rows
--   when the equal cyclic partition exists.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3069-L3081
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3069-L3081

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

theorem QEC.Coding.FiberBundle.RandomPartition.two_mul_r_le_card_selectedTypeRows
    (r typeCount : Nat) [NeZero typeCount]
    (hTypeDvd : typeCount ∣ 3 * r)
    (types : Finset (Fin typeCount))
    (hTypes : 98 * typeCount ≤ 100 * types.card) :
    2 * r ≤ (selectedTypeRows r typeCount types).card := by sorry
