-- Prove2me | Theorems.Thm_Sendov_stat_lt_one
-- name    : Sendov.stat_lt_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T20:03:01.650456+00:00
-- url     : https://prove2.me/theorems/84a6b221-d4ed-4061-966a-3e4cdb526d1a
-- title:
--   Sendov: stat lt one
-- statement:
--   **The numerical claim.**  The right-hand side of equation `stat` of the blog post is
--   strictly less than `1` for every degree `n ≥ 5` and every `0 ≤ α ≤ 17` satisfying the
--   feasibility constraint `c ^ 2 ≤ A`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Main.lean#L40-L44
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Main.lean#L40-L44

import Definitions.Def_Sendov_FiniteRange_Cover
import Definitions.Def_Sendov_LargeDegree_Endgame
import Definitions.Def_Sendov_Main
set_option autoImplicit false
open Sendov
variable {α : ℝ}

theorem Sendov.stat_lt_one {n : ℕ} (hn : 5 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17)
    (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
