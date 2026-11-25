-- Prove2me | Theorems.Thm_SCCThm8_cntLift_diff
-- name    : SCCThm8.cntLift_diff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:52:17.838073+00:00
-- url     : https://prove2.me/theorems/90b9f82b-ecb5-4c40-850f-ab1d6fda2597
-- title:
--   SCCThm8: cnt Lift diff
-- statement:
--   The difference of two lift vectors never contains both a `+2` and a `-2`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L186-L204
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L186-L204

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.cntLift_diff {n : ℕ} (v v' : Finset (Fin n)) :
    (∀ i, -1 ≤ cntLift v i - cntLift v' i) ∨ (∀ i, -1 ≤ cntLift v' i - cntLift v i) := by sorry
