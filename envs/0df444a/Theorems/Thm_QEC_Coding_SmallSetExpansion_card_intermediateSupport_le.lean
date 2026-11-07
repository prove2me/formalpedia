-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_card_intermediateSupport_le
-- name    : QEC.Coding.SmallSetExpansion.card_intermediateSupport_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:36:47.155675+00:00
-- url     : https://prove2.me/theorems/dc075ff7-bb45-474f-b806-bb820f944606
-- title:
--   Small Set Expansion: card intermediate Support le
-- statement:
--   The number of intermediate vertices reached from `S` is at most degree
--   times `|S|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L544-L568
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L544-L568

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.card_intermediateSupport_le
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat) (hRegular : IsRegular M degree)
    (S : Finset V) :
    (intermediateSupport M S).card ≤ degree * S.card := by sorry
