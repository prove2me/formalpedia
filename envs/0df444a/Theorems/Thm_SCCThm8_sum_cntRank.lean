-- Prove2me | Theorems.Thm_SCCThm8_sum_cntRank
-- name    : SCCThm8.sum_cntRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:25.787358+00:00
-- url     : https://prove2.me/theorems/961736d1-3c85-4262-a78b-4d2d6776bb2c
-- title:
--   SCCThm8: sum cnt Rank
-- statement:
--   The SCCThm8 construction uses the sum cnt Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L119-L135
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L119-L135

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.sum_cntRank {n : ℕ} (f : ℕ → ℤ) (v : Finset (Fin n)) :
    ∑ i ∈ v, f (cntRank v i) = ∑ r ∈ range v.card, f r := by sorry
