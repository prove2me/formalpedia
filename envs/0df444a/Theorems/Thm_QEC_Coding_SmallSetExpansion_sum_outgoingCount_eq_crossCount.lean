-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_outgoingCount_eq_crossCount
-- name    : QEC.Coding.SmallSetExpansion.sum_outgoingCount_eq_crossCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:33:59.321392+00:00
-- url     : https://prove2.me/theorems/374895ec-2b5f-4503-8f5d-7f53340a9b9a
-- title:
--   Small Set Expansion: sum outgoing Count eq cross Count
-- statement:
--   Outgoing mass over a set is its cross count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L518-L521
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L518-L521

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.sum_outgoingCount_eq_crossCount
    (M : WeightedGraph V) (A T : Finset V) :
    (∑ x ∈ A, outgoingCount M T x) = crossCount M A T := by sorry
