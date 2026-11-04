-- Prove2me | Theorems.Thm_ThreeSum_BooleanGreedy_choice_eq_least_w3sum_ac885d1
-- name    : ThreeSum.BooleanGreedy.choice_eq_least_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:24:20.475648+00:00
-- url     : https://prove2.me/theorems/0eb68195-2698-42cc-a542-b3948e0196b1
-- title:
--   Boolean Greedy: choice eq least
-- statement:
--   The Boolean Greedy construction uses the choice eq least property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BooleanGreedy.lean#L69-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BooleanGreedy.lean#L69-L95

import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_BooleanGreedy
set_option autoImplicit false
open ThreeSum ThreeSum.BooleanGreedy
open Finset
open scoped BigOperators

theorem ThreeSum.BooleanGreedy.choice_eq_least_w3sum_ac885d1 {matrix : ℕ → ℕ → ℕ} {rows cols : ℕ}
    (hrows : 0 < rows)
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1) (t : ℕ) :
    choice matrix rows cols t =
      LightMinimum.least (fun i => -(LightCoverScores.score matrix (active matrix rows cols t) cols i : ℤ)) rows := by sorry
