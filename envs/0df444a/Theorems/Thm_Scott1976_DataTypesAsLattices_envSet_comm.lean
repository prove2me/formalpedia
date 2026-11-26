-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_envSet_comm
-- name    : Scott1976.DataTypesAsLattices.envSet_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:34.552111+00:00
-- url     : https://prove2.me/theorems/7c4a40cc-00d2-41cd-bbfe-1ba6178dfc87
-- title:
--   Data Types As Lattices: env Set comm
-- statement:
--   The Data Types As Lattices construction uses the env Set comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L226-L236
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L226-L236

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.envSet_comm {ρ : ℕ → Pomega} {i j : ℕ} (hij : i ≠ j) (v w : Pomega) :
    envSet (envSet ρ i v) j w = envSet (envSet ρ j w) i v := by sorry
