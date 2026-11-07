-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_le_degree_mul_card_left
-- name    : QEC.Coding.SmallSetExpansion.crossCount_le_degree_mul_card_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:32:51.318638+00:00
-- url     : https://prove2.me/theorems/b5db7056-71e5-4b2e-aac2-1994280de478
-- title:
--   Small Set Expansion: cross Count le degree mul card left
-- statement:
--   In a regular weighted graph, at most `degree |S|` oriented edges leave
--   `S`, even after restricting their endpoints to an arbitrary set `T`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L378-L393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L378-L393

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.crossCount_le_degree_mul_card_left [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat) (hRegular : IsRegular M degree)
    (S T : Finset V) :
    crossCount M S T ≤ degree * S.card := by sorry
