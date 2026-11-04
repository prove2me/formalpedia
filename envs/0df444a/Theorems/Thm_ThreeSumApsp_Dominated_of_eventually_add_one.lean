-- Prove2me | Theorems.Thm_ThreeSumApsp_Dominated_of_eventually_add_one
-- name    : ThreeSumApsp.Dominated.of_eventually_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:15.059352+00:00
-- url     : https://prove2.me/theorems/53c5a1f3-e88c-4a3f-a3e0-5eb3f184eeec
-- title:
--   Dominated: of eventually add one
-- statement:
--   A bound by a nonnegative `g` that holds from some unknown point on gives a bound by `g + 1`
--   everywhere.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L271-L277
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L271-L277

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
open ThreeSumApsp.Dominated
variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

theorem ThreeSumApsp.Dominated.of_eventually_add_one {f g : ℕ → ℝ} {C : ℝ} (hfg : ∀ᶠ n in atTop, f n ≤ C * g n)
    (hg : ∀ n, 0 ≤ g n) : Dominated (fun _ => True) f fun n => g n + 1 := by sorry
