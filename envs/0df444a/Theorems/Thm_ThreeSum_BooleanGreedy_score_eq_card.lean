-- Prove2me | Theorems.Thm_ThreeSum_BooleanGreedy_score_eq_card
-- name    : ThreeSum.BooleanGreedy.score_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:24:18.999925+00:00
-- url     : https://prove2.me/theorems/13e8ae2c-b1d0-47b5-83ce-f6b4fa38912b
-- title:
--   Boolean Greedy: score eq card
-- statement:
--   The Boolean Greedy construction uses the score eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BooleanGreedy.lean#L38-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BooleanGreedy.lean#L38-L62

import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_BooleanGreedy
set_option autoImplicit false
open ThreeSum ThreeSum.BooleanGreedy
open Finset
open scoped BigOperators

theorem ThreeSum.BooleanGreedy.score_eq_card {matrix : ℕ → ℕ → ℕ} {rows cols row : ℕ}
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hrow : row < rows) (t : ℕ) :
    LightCoverScores.score matrix (active matrix rows cols t) cols row =
      ((state matrix rows cols t).filter (covers matrix row)).card := by sorry
