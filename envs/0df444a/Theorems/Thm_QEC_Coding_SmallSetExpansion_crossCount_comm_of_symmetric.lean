-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_comm_of_symmetric
-- name    : QEC.Coding.SmallSetExpansion.crossCount_comm_of_symmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:32:45.647365+00:00
-- url     : https://prove2.me/theorems/3c7a95d1-7756-4bd3-8260-b8f4d27cd4e1
-- title:
--   Small Set Expansion: cross Count comm of symmetric
-- statement:
--   A symmetric weighted graph has symmetric cross counts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L364-L374
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L364-L374

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.crossCount_comm_of_symmetric [DecidableEq V]
    (M : WeightedGraph V) (hSymm : IsSymmetric M)
    (S T : Finset V) :
    crossCount M S T = crossCount M T S := by sorry
