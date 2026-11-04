-- Prove2me | Theorems.Thm_ThreeSumApsp_Dominated_add_add
-- name    : ThreeSumApsp.Dominated.add_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:05.917256+00:00
-- url     : https://prove2.me/theorems/7eba0aea-c3da-4097-bd9c-43139bd6cc43
-- title:
--   Dominated: add add
-- statement:
--   `O(g₁) + O(g₂) = O(g₁ + g₂)` for nonnegative `g₁`, `g₂`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L169-L172
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L169-L172

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

theorem ThreeSumApsp.Dominated.add_add (h₁ : Dominated dom f₁ g₁) (h₂ : Dominated dom f₂ g₂) (hg₁ : ∀ x, dom x → 0 ≤ g₁ x)
    (hg₂ : ∀ x, dom x → 0 ≤ g₂ x) : Dominated dom (fun x => f₁ x + f₂ x) fun x => g₁ x + g₂ x := by sorry
