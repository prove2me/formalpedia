-- Prove2me | Theorems.Thm_SCCThm8_cntLift_eq_neg_one
-- name    : SCCThm8.cntLift_eq_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:51:56.352156+00:00
-- url     : https://prove2.me/theorems/3eed7ba1-dbc7-4179-ace8-0dddebf67eb3
-- title:
--   SCCThm8: cnt Lift eq neg one
-- statement:
--   The SCCThm8 construction uses the cnt Lift eq neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L167-L171
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L167-L171

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.cntLift_eq_neg_one {n : ℕ} {v : Finset (Fin n)} {i : Fin n} (h : cntLift v i = -1) :
    i ∈ v ∧ ¬ 2 * cntRank v i < v.card := by sorry
