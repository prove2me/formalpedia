-- Prove2me | Theorems.Thm_SCCThm8_mem_ite_insert
-- name    : SCCThm8.mem_ite_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:18.199044+00:00
-- url     : https://prove2.me/theorems/9aa6dfc1-2f83-4cb8-839f-d562ec14c86a
-- title:
--   SCCThm8: mem ite insert
-- statement:
--   The SCCThm8 construction uses the mem ite insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L13-L15
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L13-L15

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.mem_ite_insert {α : Type*} [DecidableEq α] (c : Prop) [Decidable c] (x i : α)
    (A : Finset α) : i ∈ (if c then insert x A else A) ↔ (c ∧ i = x) ∨ i ∈ A := by sorry
