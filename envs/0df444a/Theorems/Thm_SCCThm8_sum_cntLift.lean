-- Prove2me | Theorems.Thm_SCCThm8_sum_cntLift
-- name    : SCCThm8.sum_cntLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:35.742494+00:00
-- url     : https://prove2.me/theorems/2e57f8c5-38fc-499a-9ffa-01c3b3920f96
-- title:
--   SCCThm8: sum cnt Lift
-- statement:
--   The SCCThm8 construction uses the sum cnt Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L137-L155
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L137-L155

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.sum_cntLift {n : ℕ} (v : Finset (Fin n)) (hv : Even v.card) :
    ∑ i, cntLift v i = 0 := by sorry
