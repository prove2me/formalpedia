-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_incomingCount_le_degree
-- name    : QEC.Coding.SmallSetExpansion.incomingCount_le_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:36:41.212189+00:00
-- url     : https://prove2.me/theorems/c8a75de6-66b2-40bd-9f2f-e0eb5a3dd5eb
-- title:
--   Small Set Expansion: incoming Count le degree
-- statement:
--   In a symmetric regular graph, incoming multiplicity from any subset is
--   bounded by the degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L525-L540
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L525-L540

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.incomingCount_le_degree
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (S : Finset V) (x : V) :
    incomingCount M S x ≤ degree := by sorry
