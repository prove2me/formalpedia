-- Prove2me | Theorems.Thm_ThreeSumApsp_isBigO_comp_add_one
-- name    : ThreeSumApsp.isBigO_comp_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:59.785103+00:00
-- url     : https://prove2.me/theorems/25c240e2-8aa3-4115-8910-812f17f3a02d
-- title:
--   Three Sum Apsp: is Big O comp add one
-- statement:
--   If `G = O(g)` with `g ≥ 0`, then `G(size n) = O(g(size n) + 1)` for every `size : ℕ → ℕ`. The
--   sizes need not tend to infinity; the `+ 1` covers the finitely many sizes at which the bound does
--   not hold yet.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L292-L298
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L292-L298

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp

theorem ThreeSumApsp.isBigO_comp_add_one {G g : ℕ → ℝ} (hG : G =O[atTop] g) (hg : ∀ s, 0 ≤ g s)
    (size : ℕ → ℕ) : (fun n => G (size n)) =O[atTop] fun n => g (size n) + 1 := by sorry
