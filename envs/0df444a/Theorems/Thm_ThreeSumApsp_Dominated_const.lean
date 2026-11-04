-- Prove2me | Theorems.Thm_ThreeSumApsp_Dominated_const
-- name    : ThreeSumApsp.Dominated.const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:55.864275+00:00
-- url     : https://prove2.me/theorems/43deeb2f-08be-4f9e-93cb-ec8ae64ca56b
-- title:
--   Dominated: const
-- statement:
--   A constant is `O(g)` when `g ≥ 1` on the domain.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L105-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L105-L107

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

theorem ThreeSumApsp.Dominated.const (c : ℝ) (hg : ∀ x, dom x → 1 ≤ g x) : Dominated dom (fun _ => c) g := by sorry
