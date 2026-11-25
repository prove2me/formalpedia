-- Prove2me | Theorems.Thm_SCCThm8_mem_iff_cntLift_ne
-- name    : SCCThm8.mem_iff_cntLift_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:51:57.503293+00:00
-- url     : https://prove2.me/theorems/cc2dcc04-5e5b-4910-9f34-4edb74131eab
-- title:
--   SCCThm8: mem iff cnt Lift ne
-- statement:
--   The SCCThm8 construction uses the mem iff cnt Lift ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L173-L176
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L173-L176

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.mem_iff_cntLift_ne {n : ℕ} (v : Finset (Fin n)) (i : Fin n) :
    i ∈ v ↔ cntLift v i ≠ 0 := by sorry
