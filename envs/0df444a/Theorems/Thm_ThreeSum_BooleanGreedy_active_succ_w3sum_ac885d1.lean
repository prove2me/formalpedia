-- Prove2me | Theorems.Thm_ThreeSum_BooleanGreedy_active_succ_w3sum_ac885d1
-- name    : ThreeSum.BooleanGreedy.active_succ_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:24:23.931175+00:00
-- url     : https://prove2.me/theorems/9dcd3f28-ad60-468b-bb02-802a99f28604
-- title:
--   Boolean Greedy: active succ
-- statement:
--   The Boolean Greedy construction uses the active succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BooleanGreedy.lean#L97-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BooleanGreedy.lean#L97-L116

import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_BooleanGreedy
set_option autoImplicit false
open ThreeSum ThreeSum.BooleanGreedy
open Finset
open scoped BigOperators

theorem ThreeSum.BooleanGreedy.active_succ_w3sum_ac885d1 {matrix : ℕ → ℕ → ℕ} {rows cols : ℕ}
    (hrows : 0 < rows)
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1) (t j : ℕ) (hj : j < cols) :
    active matrix rows cols (t+1) j =
      active matrix rows cols t j * (1-matrix (choice matrix rows cols t) j) := by sorry
