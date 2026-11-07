-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_incomingCount_eq_crossCount
-- name    : QEC.Coding.SmallSetExpansion.sum_incomingCount_eq_crossCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:33:53.651828+00:00
-- url     : https://prove2.me/theorems/1573d7dc-b86e-42c3-877f-eaf939864f73
-- title:
--   Small Set Expansion: sum incoming Count eq cross Count
-- statement:
--   Incoming mass becomes an ordinary cross count when the graph is
--   symmetric.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L506-L515
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L506-L515

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.sum_incomingCount_eq_crossCount
    (M : WeightedGraph V) (hSymm : IsSymmetric M)
    (S A : Finset V) :
    (∑ x ∈ A, incomingCount M S x) = crossCount M A S := by sorry
