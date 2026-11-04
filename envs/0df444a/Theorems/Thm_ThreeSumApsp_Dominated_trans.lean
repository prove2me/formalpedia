-- Prove2me | Theorems.Thm_ThreeSumApsp_Dominated_trans
-- name    : ThreeSumApsp.Dominated.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:51:46.15664+00:00
-- url     : https://prove2.me/theorems/91d563cf-71b7-4262-b306-24463f153485
-- title:
--   Dominated: trans
-- statement:
--   `f = O(g)` and `g = O(h)` give `f = O(h)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L124-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L124-L130

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
set_option autoImplicit false
public section
open Filter Asymptotics
open ThreeSumApsp
open ThreeSumApsp.Dominated
variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

theorem ThreeSumApsp.Dominated.trans (hfg : Dominated dom f g) (hgh : Dominated dom g h) :
    Dominated dom f h := by sorry
