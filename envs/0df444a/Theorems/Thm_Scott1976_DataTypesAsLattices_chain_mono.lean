-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_chain_mono
-- name    : Scott1976.DataTypesAsLattices.chain_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:59.120315+00:00
-- url     : https://prove2.me/theorems/fd43d899-b0eb-449e-9109-764e5a3e5a9e
-- title:
--   Data Types As Lattices: chain mono
-- statement:
--   The Data Types As Lattices construction uses the chain mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L71-L79
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L71-L79

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.chain_mono (xs : ℕ → Pomega) (hmono : ∀ n, xs n ⊆ xs (n + 1)) :
    ∀ a b, a ≤ b → xs a ⊆ xs b := by sorry
