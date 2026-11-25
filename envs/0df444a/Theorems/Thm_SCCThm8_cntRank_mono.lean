-- Prove2me | Theorems.Thm_SCCThm8_cntRank_mono
-- name    : SCCThm8.cntRank_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:51:58.731959+00:00
-- url     : https://prove2.me/theorems/e1eae2fc-10d8-53af-8b57-8be74dbc16d7
-- title:
--   SCCThm8: cnt Rank mono
-- statement:
--   The SCCThm8 construction uses the cnt Rank mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L178-L183
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L178-L183

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.cntRank_mono {n : ℕ} (v : Finset (Fin n)) {i j : Fin n} (h : i < j) :
    cntRank v i ≤ cntRank v j := by sorry
